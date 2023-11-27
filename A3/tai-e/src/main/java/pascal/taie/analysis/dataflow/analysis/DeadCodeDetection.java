/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        // mark all reached stmt

        var unreachedStmt = new HashSet<Stmt>(cfg.getNodes());
        var workList = new LinkedList<Stmt>();
        workList.add(cfg.getEntry());
        // cfg相对ir的stmts会添加entry和exit两个节点
        // exit节点不应该出现在结果中
        unreachedStmt.remove(cfg.getExit());
        // iterate cfg
        while (!workList.isEmpty()){
            var stmt = workList.pop();
            unreachedStmt.remove(stmt);
            // unused variable
            if (isUnusedVar(stmt,liveVars)){
                deadCode.add(stmt);
            }

            // if and switch
            if (stmt instanceof If ifStmt){
                var condition = ifStmt.getCondition();
                var cpFact = constants.getResult(stmt);
                var value = ConstantPropagation.evaluate(condition,cpFact);

                for (Edge<Stmt> stmtEdge : cfg.getOutEdgesOf(stmt)) {
                    if (value.isNAC() || (stmtEdge.getKind() == Edge.Kind.IF_TRUE && value.getConstant() == 1)){
                        var target = stmtEdge.getTarget();
                        if (unreachedStmt.contains(target)){
                            workList.add(target);
                        }
                    }

                    if (value.isNAC() || (stmtEdge.getKind() == Edge.Kind.IF_FALSE && value.getConstant() == 0)){
                        var target = stmtEdge.getTarget();
                        if (unreachedStmt.contains(target)){
                            workList.add(target);
                        }
                    }
                }
            } else if (stmt instanceof SwitchStmt switchStmt){
                var switchVar = switchStmt.getVar();
                var value = constants.getResult(stmt).get(switchVar);
                if (value.isNAC()){
                    for (Stmt succStmt : cfg.getSuccsOf(stmt)) {
                        if (unreachedStmt.contains(succStmt)){
                            workList.add(succStmt);
                        }
                    }
                } else {
                    var consValue = value.getConstant();
                    Edge<Stmt> defaultEdge = null;
                    var isMatch = false;
                    for (Edge<Stmt> stmtEdge : cfg.getOutEdgesOf(stmt)) {
                        if(stmtEdge.getKind() == Edge.Kind.SWITCH_DEFAULT){
                            defaultEdge = stmtEdge;
                            continue;
                        }

                        if (stmtEdge.getKind() == Edge.Kind.SWITCH_CASE){
                            if (consValue == stmtEdge.getCaseValue()){
                                isMatch = true;
                                var target = stmtEdge.getTarget();
                                if (unreachedStmt.contains(target)){
                                    workList.add(target);
                                }
                            }
                        }
                    }

                    if (!isMatch && defaultEdge != null){
                        var target = defaultEdge.getTarget();
                        if (unreachedStmt.contains(target)){
                            workList.add(target);
                        }
                    }
                }
            } else {
                for (Stmt succStmt : cfg.getSuccsOf(stmt)) {
                    if (unreachedStmt.contains(succStmt)){
                        workList.add(succStmt);
                    }
                }
            }
        }

        deadCode.addAll(unreachedStmt);

        return deadCode;
    }

    private boolean isUnusedVar(Stmt node,DataflowResult<Stmt,SetFact<Var>> liveVars){
        var defVar = node.getDef();
        if (defVar.isEmpty()){
            return false;
        }

        for (RValue use : node.getUses()) {
            if (!hasNoSideEffect(use)){
                return false;
            }
        }

        if (defVar.get() instanceof Var v){
            return !liveVars.getResult(node).contains(v);
        }
        return false;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
