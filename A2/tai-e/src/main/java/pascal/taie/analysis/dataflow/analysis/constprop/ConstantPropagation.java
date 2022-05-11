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

import jas.CP;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

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
        CPFact fact = new CPFact();
        for (Var var : cfg.getIR().getParams()) {
            fact.update(var, Value.getNAC());
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
        for (Var key : fact.keySet()) {
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v3) {
        // TODO - finish me
        if (v1.isNAC() || v3.isNAC()) { return Value.getNAC(); }
        // reduce memory
        if (v1.isUndef()) { return v3; }
        if (v3.isUndef()) { return v1; }
        if (v1.getConstant() == v3.getConstant()) { return v1; }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact outCopy = in.copy();

        if (stmt.getDef().isPresent()) {
            LValue lValue = stmt.getDef().get();
            if (lValue instanceof Var lVar) {
//                outCopy.update(lVar, evaluate(stmt.getUses().get(stmt.getUses().size() - 1), in));
                for (RValue rValue : stmt.getUses()) {
                    Value eval = evaluate(rValue, outCopy);
                    if (rValue == stmt.getUses().get(stmt.getUses().size() - 1)) {
                        outCopy.remove(lVar);
                        outCopy.update(lVar, eval);
                    }
                }
            }
        }
        else {
            for (RValue rValue : stmt.getUses()) {
                Value eval = evaluate(rValue, outCopy);
            }
        }
        if (out.equals(outCopy)) {
            return false;
        }
        out.clear();
        out.copyFrom(outCopy);
        return true;
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
        if (exp instanceof Var expr) {
            return in.get(expr);
        }
        else if (exp instanceof IntLiteral expr) {
            return Value.makeConstant(expr.getValue());
        }
        else if (exp instanceof BinaryExp expBin) {
            Var operand1 = expBin.getOperand1();
            Var operand2 = expBin.getOperand2();

//            if (in.get(operand1).isUndef()) { in.update(operand1, Value.getNAC()); }
//            if (in.get(operand2).isUndef()) { in.update(operand2, Value.getNAC()); }

            if (in.get(operand1).isConstant() && in.get(operand2).isConstant()) {
                int val1 = in.get(operand1).getConstant();
                int val2 = in.get(operand2).getConstant();

                if (exp instanceof ArithmeticExp expr) {
                    ArithmeticExp.Op op = expr.getOperator();
                    switch (op) {
                        case ADD -> { return Value.makeConstant(val1 + val2); }
                        case SUB -> { return Value.makeConstant(val1 - val2); }
                        case MUL -> { return Value.makeConstant(val1 * val2); }
                        case DIV -> { return Value.makeConstant(val1 / val2); }
                        case REM -> { return Value.makeConstant(val1 % val2); }
                    }
                }
                else if (exp instanceof BitwiseExp expr) {
                    BitwiseExp.Op op = expr.getOperator();
                    switch (op) {
                        case OR -> { return Value.makeConstant(val1 | val2); }
                        case AND -> { return Value.makeConstant(val1 & val2); }
                        case XOR -> { return Value.makeConstant(val1 ^ val2); }
                    }
                }
                else if (exp instanceof ConditionExp expr) {
                    ConditionExp.Op op = expr.getOperator();
                    switch (op) {
                        case EQ -> { return Value.makeConstant(val1 == val2 ? 1 : 0); }
                        case NE -> { return Value.makeConstant(val1 != val2 ? 1 : 0); }
                        case LT -> { return Value.makeConstant(val1 <  val2 ? 1 : 0); }
                        case GT -> { return Value.makeConstant(val1 >  val2 ? 1 : 0); }
                        case LE -> { return Value.makeConstant(val1 <= val2 ? 1 : 0); }
                        case GE -> { return Value.makeConstant(val1 >= val2 ? 1 : 0); }
                    }
                }
                else if (exp instanceof ShiftExp expr) {
                    ShiftExp.Op op = expr.getOperator();
                    switch (op) {
                        case SHL -> { return Value.makeConstant(val1 << val2); }
                        case SHR -> { return Value.makeConstant(val1 >> val2); }
                        case USHR -> { return Value.makeConstant(val1 >>> val2); }
                    }
                }
            }
            else if (in.get(operand1).isNAC() || in.get(operand2).isNAC()) {
                return Value.getNAC();
            }
            else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
