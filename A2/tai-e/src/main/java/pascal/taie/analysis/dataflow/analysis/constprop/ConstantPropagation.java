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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        var fact = new CPFact();
        //将所有变量设置为UNDEF
        for (Var var : cfg.getIR().getVars()) {
            fact.update(var, Value.getUndef());
        }
        //设置参数为NAC
        for (Var param : cfg.getIR().getParams()) {
            //必须判断是否可以持有int
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.entries().forEach(entry -> {
            target.update(entry.getKey(), meetValue(entry.getValue(), target.get(entry.getKey())));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isUndef() || v2.isUndef()) {
            return v1.isUndef() ? v2 : v1;
        }

        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return Value.makeConstant(v1.getConstant());
            } else {
                return Value.getNAC();
            }
        }

        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var newOutFact = in.copy();
        //注意判断defVar是否可以holdInt
        if (stmt instanceof DefinitionStmt<?, ?> assignStmt) {
            var def = assignStmt.getDef().orElse(null);
            if (def instanceof Var defVar && canHoldInt(defVar)) {
                newOutFact.update(defVar, evaluate(assignStmt.getRValue(), newOutFact));
            }
        }
        //如果inFact中清除了值，会导致判断错误
        if (newOutFact.equals(out)) {
            return false;
        } else {
            out.clear();
            out.copyFrom(newOutFact);
            return true;
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof Var var) {
            return in.get(var);
        } else if (exp instanceof BinaryExp binaryExp) {
            var leftVar = binaryExp.getOperand1();
            var rightVar = binaryExp.getOperand2();
            var leftValue = in.get(leftVar);
            var rightValue = in.get(rightVar);

            if (rightValue.isConstant() && rightValue.getConstant() == 0
                    && (binaryExp.getOperator() == ArithmeticExp.Op.DIV || binaryExp.getOperator() == ArithmeticExp.Op.REM)) {
                return Value.getUndef();
            }

            if (leftValue.isNAC() || rightValue.isNAC()) {
                return Value.getNAC();
            }

            if (leftValue.isConstant() && rightValue.isConstant()) {
                if (exp instanceof ArithmeticExp arithmeticExp) {
                    return switch (arithmeticExp.getOperator()) {
                        case ADD -> Value.makeConstant(leftValue.getConstant() + rightValue.getConstant());
                        case SUB -> Value.makeConstant(leftValue.getConstant() - rightValue.getConstant());
                        case DIV -> Value.makeConstant(leftValue.getConstant() / rightValue.getConstant());
                        case MUL -> Value.makeConstant(leftValue.getConstant() * rightValue.getConstant());
                        case REM -> Value.makeConstant(leftValue.getConstant() % rightValue.getConstant());
                    };
                } else if (exp instanceof BitwiseExp bitwiseExp) {
                    return switch (bitwiseExp.getOperator()) {
                        case OR -> Value.makeConstant(leftValue.getConstant() | rightValue.getConstant());
                        case AND -> Value.makeConstant(leftValue.getConstant() & rightValue.getConstant());
                        case XOR -> Value.makeConstant(leftValue.getConstant() ^ rightValue.getConstant());
                    };
                } else if (exp instanceof ShiftExp shiftExp) {
                    return Value.makeConstant(
                            switch (shiftExp.getOperator()) {
                                case SHL -> leftValue.getConstant() << rightValue.getConstant();
                                case SHR -> leftValue.getConstant() >> rightValue.getConstant();
                                case USHR -> leftValue.getConstant() >>> rightValue.getConstant();
                            }
                    );
                } else if (exp instanceof ConditionExp conditionExp) {
                    return switch (conditionExp.getOperator()) {
                        case EQ -> Value.makeConstant(leftValue.getConstant() == rightValue.getConstant() ? 1 : 0);
                        case GE -> Value.makeConstant(leftValue.getConstant() >= rightValue.getConstant() ? 1 : 0);
                        case GT -> Value.makeConstant(leftValue.getConstant() > rightValue.getConstant() ? 1 : 0);
                        case LE -> Value.makeConstant(leftValue.getConstant() <= rightValue.getConstant() ? 1 : 0);
                        case LT -> Value.makeConstant(leftValue.getConstant() < rightValue.getConstant() ? 1 : 0);
                        case NE -> Value.makeConstant(leftValue.getConstant() != rightValue.getConstant() ? 1 : 0);
                    };
                }
            }
            return Value.getUndef();
        }
        //处理不了的认为是nac
        return Value.getNAC();
    }
}
