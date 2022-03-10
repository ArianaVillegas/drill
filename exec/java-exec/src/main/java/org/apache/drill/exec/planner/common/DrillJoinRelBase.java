/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.drill.exec.planner.common;

import java.util.*;

import org.apache.calcite.plan.*;
import org.apache.calcite.plan.volcano.RelSubset;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.CorrelationId;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.logical.LogicalJoin;
import org.apache.calcite.rel.metadata.RelColumnOrigin;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexTableInputRef;
import org.apache.calcite.util.ImmutableBitSet;
import org.apache.calcite.util.Pair;
import org.apache.drill.common.expression.SchemaPath;
import org.apache.drill.exec.ExecConstants;
import org.apache.drill.exec.expr.holders.IntHolder;
import org.apache.drill.exec.physical.impl.join.JoinUtils;
import org.apache.drill.exec.physical.impl.join.JoinUtils.JoinCategory;
import org.apache.drill.exec.physical.impl.scan.file.MetadataColumn;
import org.apache.drill.exec.planner.cost.DrillCostBase;
import org.apache.drill.exec.planner.cost.DrillCostBase.DrillCostFactory;
import org.apache.drill.exec.planner.logical.DrillJoin;
import org.apache.drill.exec.planner.logical.DrillTable;
import org.apache.drill.exec.planner.physical.PrelUtil;
import org.apache.drill.metastore.statistics.Histogram;
import org.apache.drill.shaded.guava.com.google.common.collect.Lists;

import org.apache.drill.exec.util.Utilities;

/**
 * Base class for logical and physical Joins implemented in Drill.
 */
public abstract class DrillJoinRelBase extends Join implements DrillJoin {
  protected List<Integer> leftKeys = Lists.newArrayList();
  protected List<Integer> rightKeys = Lists.newArrayList();

  /**
   * The join key positions for which null values will not match.
   */
  protected List<Boolean> filterNulls = Lists.newArrayList();
  private final double joinRowFactor;

  public DrillJoinRelBase(RelOptCluster cluster, RelTraitSet traits, RelNode left, RelNode right, RexNode condition,
      JoinRelType joinType) {
    super(cluster, traits, left, right, condition,
        CorrelationId.setOf(Collections.<String> emptySet()), joinType);
    this.joinRowFactor = PrelUtil.getPlannerSettings(cluster.getPlanner()).getRowCountEstimateFactor();
  }

  @Override
  public RelOptCost computeSelfCost(RelOptPlanner planner, RelMetadataQuery mq) {
    // System.out.println("Estimate join cost");
    JoinCategory category = JoinUtils.getJoinCategory(left, right, condition, leftKeys, rightKeys, filterNulls);
    if (category == JoinCategory.CARTESIAN || category == JoinCategory.INEQUALITY) {
      if (PrelUtil.getPlannerSettings(planner).isNestedLoopJoinEnabled()) {
        if (PrelUtil.getPlannerSettings(planner).isNlJoinForScalarOnly()) {
          if (JoinUtils.hasScalarSubqueryInput(left, right)) {
            return computeLogicalJoinCost(planner, mq);
          } else {
            /*
             *  Why do we return non-infinite cost for CartsianJoin with non-scalar subquery, when LOPT planner is enabled?
             *   - We do not want to turn on the two Join permutation rule : PushJoinPastThroughJoin.LEFT, RIGHT.
             *   - As such, we may end up with filter on top of join, which will cause CanNotPlan in LogicalPlanning, if we
             *   return infinite cost.
             *   - Such filter on top of join might be pushed into JOIN, when LOPT planner is called.
             *   - Return non-infinite cost will give LOPT planner a chance to try to push the filters.
             */
            if (PrelUtil.getPlannerSettings(planner).isHepOptEnabled()) {
             return computeCartesianJoinCost(planner, mq);
            } else {
              return planner.getCostFactory().makeInfiniteCost();
            }
          }
        } else {
          return computeLogicalJoinCost(planner, mq);
        }
      }
      return planner.getCostFactory().makeInfiniteCost();
    }

    return computeLogicalJoinCost(planner, mq);
  }

  private double estimateJoinCardinality(Double[] left, Double[] right) {
    Double cnt = 0.0;
    for (int i=1; i<left.length; i++) {
      for (int j=1; j<right.length; j++) {
        if (right[j-1] > left[i] || left[i-1] > right[j]) continue;
        cnt += 1;
      }
    }
    return cnt;
  }

  private DrillStatsTable getTable(Set<RexTableInputRef.RelTableRef> tables, String col_name) {
    for (RexTableInputRef.RelTableRef table:tables) {
      DrillTable drillTable = Utilities.getDrillTable(table.getTable());
      if (drillTable == null) {
        continue;
      }
      DrillStatsTable drillStatsTable = drillTable.getMetadataProviderManager().getStatsProvider();
      if (drillStatsTable == null) {
        continue;
      }
      Set<SchemaPath> columns = drillStatsTable.getColumns();
      if (columns.contains(SchemaPath.parseFromString(col_name))) {
        return drillStatsTable;
      }
    }
    return null;
  }

  @Override
  public double estimateRowCount(RelMetadataQuery mq) {
    if (this.condition.isAlwaysTrue()) {
      return joinRowFactor * this.getLeft().estimateRowCount(mq) * this.getRight().estimateRowCount(mq);
    }

    LogicalJoin jr = LogicalJoin.create(this.getLeft(), this.getRight(), this.getCondition(),
            this.getVariablesSet(), this.getJoinType());

    if (!DrillRelOptUtil.guessRows(this)         //Statistics present for left and right side of the join
        && jr.getJoinType() == JoinRelType.INNER) {
      // System.out.println("Estimate row count join cost");
      List<Pair<Integer, Integer>> joinConditions = DrillRelOptUtil.analyzeSimpleEquiJoin((Join)jr);
      if (joinConditions.size() > 0) {
        List<Integer> leftSide =  new ArrayList<>();
        List<Integer> rightSide = new ArrayList<>();
        for (Pair<Integer, Integer> condition : joinConditions) {
          leftSide.add(condition.left);
          rightSide.add(condition.right);
        }
        ImmutableBitSet leq = ImmutableBitSet.of(leftSide);
        ImmutableBitSet req = ImmutableBitSet.of(rightSide);

        Double ldrc = mq.getDistinctRowCount(this.getLeft(), leq, null);
        Double rdrc = mq.getDistinctRowCount(this.getRight(), req, null);

        Double lrc = mq.getRowCount(this.getLeft());
        Double rrc = mq.getRowCount(this.getRight());

        Set<RexTableInputRef.RelTableRef> tables_left = mq.getTableReferences(this.getLeft());
        Set<RexTableInputRef.RelTableRef> tables_right = mq.getTableReferences(this.getRight());
        String name_left = this.getLeft().getRowType().getFieldNames().get(leq.nth(0));
        String name_right = this.getRight().getRowType().getFieldNames().get(req.nth(0));

        System.out.println(name_left + ":" + name_right);

        if (tables_left != null && tables_right != null && ldrc != null && rdrc != null && lrc != null && rrc != null) {
          DrillStatsTable stats_left = getTable(tables_left, name_left);
          DrillStatsTable stats_right = getTable(tables_right, name_right);
          SchemaPath col_name_left = SchemaPath.parseFromString(name_left);
          SchemaPath col_name_right = SchemaPath.parseFromString(name_right);
          // System.out.println(stats_left.getTableName() + " " + stats_right.getTableName());

          NumericEquiDepthHistogram hist_left = (NumericEquiDepthHistogram) stats_left.getHistogram(col_name_left);
          NumericEquiDepthHistogram hist_right = (NumericEquiDepthHistogram) stats_right.getHistogram(col_name_right);
          double factor = lrc * rrc;
          double card = estimateJoinCardinality(hist_left.getBuckets(), hist_right.getBuckets()) * Math.max(hist_left.getNumRowsPerBucket(), hist_right.getNumRowsPerBucket());
          /*System.out.printf("Cardinality %f\n", card);
          System.out.printf("Hist: %f -- %f\n", hist_left.getNumRowsPerBucket(), hist_right.getNumRowsPerBucket());
          System.out.printf("Estimate row count join cost %f\n", (card==0) ? 0 : (lrc/card)*rrc);
          System.out.printf("Prev Estimate row count join cost %f\n", (lrc / Math.max(ldrc, rdrc)) * rrc);
          System.out.printf("RowCnt: %f -- %f\n", lrc, rrc);*/
          return (card==0) ? 0 : (lrc/card)*rrc*1000;
        }

        if (ldrc != null && rdrc != null && lrc != null && rrc != null) {
          // Join cardinality = (lrc * rrc) / Math.max(ldrc, rdrc). Avoid overflow by dividing earlier
          return (lrc / Math.max(ldrc, rdrc)) * rrc;
        }
      }
    }

    return joinRowFactor * Math.max(
        mq.getRowCount(this.getLeft()),
        mq.getRowCount(this.getRight()));
  }

  /**
   * Returns whether there are any elements in common between left and right.
   */
  private static <T> boolean intersects(List<T> left, List<T> right) {
    return new HashSet<>(left).removeAll(right);
  }

  public static boolean uniqueFieldNames(RelDataType rowType) {
    return isUnique(rowType.getFieldNames());
  }

  public static <T> boolean isUnique(List<T> list) {
    return new HashSet<>(list).size() == list.size();
  }

  public List<Integer> getLeftKeys() {
    return this.leftKeys;
  }

  public List<Integer> getRightKeys() {
    return this.rightKeys;
  }

  protected  RelOptCost computeCartesianJoinCost(RelOptPlanner planner, RelMetadataQuery mq) {
    final double probeRowCount = mq.getRowCount(this.getLeft());
    final double buildRowCount = mq.getRowCount(this.getRight());

    final DrillCostFactory costFactory = (DrillCostFactory) planner.getCostFactory();

    final double mulFactor = 10000; // This is a magic number,
                                    // just to make sure Cartesian Join is more expensive
                                    // than Non-Cartesian Join.

    final int keySize = 1;  // assume having 1 join key, when estimate join cost.
    final DrillCostBase cost = (DrillCostBase) computeHashJoinCostWithKeySize(planner, keySize, mq).multiplyBy(mulFactor);

    // Cartesian join row count will be product of two inputs. The other factors come from the above estimated DrillCost.
    return costFactory.makeCost(
        buildRowCount * probeRowCount,
        cost.getCpu(),
        cost.getIo(),
        cost.getNetwork(),
        cost.getMemory() );

  }

  protected RelOptCost computeLogicalJoinCost(RelOptPlanner planner, RelMetadataQuery mq) {
    // During Logical Planning, although we don't care much about the actual physical join that will
    // be chosen, we do care about which table - bigger or smaller - is chosen as the right input
    // of the join since that is important at least for hash join and we don't currently have
    // hybrid-hash-join that can swap the inputs dynamically.  The Calcite planner's default cost of a join
    // is the same whether the bigger table is used as left input or right. In order to overcome that,
    // we will use the Hash Join cost as the logical cost such that cardinality of left and right inputs
    // is considered appropriately.
    return computeHashJoinCost(planner, mq);
  }

  protected RelOptCost computeHashJoinCost(RelOptPlanner planner, RelMetadataQuery mq) {
      return computeHashJoinCostWithKeySize(planner, this.getLeftKeys().size(), mq);
  }

  /**
   *
   * @param planner  : Optimization Planner.
   * @param keySize  : the # of join keys in join condition. Left key size should be equal to right key size.
   * @return         : RelOptCost
   */
  private RelOptCost computeHashJoinCostWithKeySize(RelOptPlanner planner, int keySize, RelMetadataQuery mq) {
    double probeRowCount = mq.getRowCount(this.getLeft());
    double buildRowCount = mq.getRowCount(this.getRight());
    // System.out.println("probeRowCount " + probeRowCount + " buildRowCount " + buildRowCount);
    return computeHashJoinCostWithRowCntKeySize(planner, probeRowCount, buildRowCount, keySize);
  }

  public static RelOptCost computeHashJoinCostWithRowCntKeySize(RelOptPlanner planner, double probeRowCount,
                                                                double buildRowCount, int keySize) {
    // cpu cost of hashing the join keys for the build side
    double cpuCostBuild = DrillCostBase.HASH_CPU_COST * keySize * buildRowCount;
    // cpu cost of hashing the join keys for the probe side
    double cpuCostProbe = DrillCostBase.HASH_CPU_COST * keySize * probeRowCount;

    // cpu cost of evaluating each leftkey=rightkey join condition
    double joinConditionCost = DrillCostBase.COMPARE_CPU_COST * keySize;

    double factor = PrelUtil.getPlannerSettings(planner).getOptions()
        .getOption(ExecConstants.HASH_JOIN_TABLE_FACTOR_KEY).float_val;
    long fieldWidth = PrelUtil.getPlannerSettings(planner).getOptions()
        .getOption(ExecConstants.AVERAGE_FIELD_WIDTH_KEY).num_val;

    // table + hashValues + links
    double memCost =
        (
            (fieldWidth * keySize) +
                IntHolder.WIDTH +
                IntHolder.WIDTH
        ) * buildRowCount * factor;

    double cpuCost = joinConditionCost * (probeRowCount) // probe size determine the join condition comparison cost
        + cpuCostBuild + cpuCostProbe;

    DrillCostFactory costFactory = (DrillCostFactory) planner.getCostFactory();

    return costFactory.makeCost(buildRowCount + probeRowCount, cpuCost, 0, 0, memCost);
  }

}
