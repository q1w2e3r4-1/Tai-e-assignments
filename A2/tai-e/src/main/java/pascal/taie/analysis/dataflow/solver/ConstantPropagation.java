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
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        CPFact fact = new CPFact();
        for(Var param: cfg.getIR().getParams()) {
            if(canHoldInt(param)){
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for(Var var: fact.keySet()){
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            target.update(var, meetValue(v1, v2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if(v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }

        if(v1.isUndef()) return v2;
        if(v2.isUndef()) return v1;

        assert(v1.isConstant() && v2.isConstant());

        if(v1.getConstant() == v2.getConstant()){
            return Value.makeConstant(v1.getConstant());
        }
        else{
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact result = in.copy();
        if(stmt instanceof DefinitionStmt<?,?>){
            // 注意这里使用的都是DefinitionStmt<LValue, RValue>的方法，因为stmt的get和def一个是Optional一个是数组，而stmt的use exp是树状结构
            LValue lValue = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if(lValue instanceof Var def && canHoldInt(def)){
                RValue exp = ((DefinitionStmt<?, ?>) stmt).getRValue();
                // 我们只分析赋值语句 (有一个左值的语句)
                result.update(def, evaluate(exp, result));
            }
            // else, 可能是字段赋值等，我们暂时还处理不了它们 pass

        }
        return out.copyFrom(result);
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
        // BinaryExp 的两个操作数都是 Var 类型的
        if(exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if(exp instanceof Var){
            return in.get((Var)exp);
        }
        else if(exp instanceof BinaryExp){
            Value op1 = in.get(((BinaryExp) exp).getOperand1());
            Value op2 = in.get(((BinaryExp) exp).getOperand2());
            if(op1.isConstant() && op2.isConstant()){
                return calculate(op1, op2, (BinaryExp)exp);
            }
            else if(op1.isNAC() || op2.isNAC()){
                if (op1.isNAC() && op2.isConstant() && exp instanceof ArithmeticExp) {
                    ArithmeticExp.Op operator = ((ArithmeticExp) exp).getOperator();
                    if (operator == ArithmeticExp.Op.DIV || operator == ArithmeticExp.Op.REM) {
                        if (op2.getConstant() == 0) return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }
            else{
                return Value.getUndef();
            }
        }
        else{
            // Inter-procedural .etc
//            System.out.println("Another exp type???");
            return Value.getNAC();
        }
    }

    public static Value calculate(Value op1, Value op2, BinaryExp exp){
        int x = op1.getConstant();
        int y = op2.getConstant();

        if(exp instanceof ArithmeticExp){
            ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
            return switch (op) {
                case ADD -> Value.makeConstant(x + y);
                case SUB -> Value.makeConstant(x - y);
                case MUL -> Value.makeConstant(x * y);
                case DIV -> y == 0? Value.getUndef() : Value.makeConstant(x / y);
                case REM -> y == 0? Value.getUndef() : Value.makeConstant(x % y);
            };
        }
        else if(exp instanceof BitwiseExp){
            BitwiseExp.Op op = ((BitwiseExp) exp).getOperator();
            return switch (op) {
                case OR -> Value.makeConstant(x | y);
                case AND -> Value.makeConstant(x & y);
                case XOR -> Value.makeConstant(x ^ y);
            };
        }
        else if(exp instanceof ShiftExp){
            ShiftExp.Op op = ((ShiftExp) exp).getOperator();
            return switch (op) {
                case SHL -> Value.makeConstant(x << y);
                case SHR -> Value.makeConstant(x >> y);
                case USHR -> Value.makeConstant(x >>> y);
            };
        }
        else if(exp instanceof ConditionExp){
            ConditionExp.Op op = ((ConditionExp) exp).getOperator();
            boolean b = switch (op) {
                case EQ -> x == y;
                case NE -> x != y;
                case GT -> x > y;
                case GE -> x >= y;
                case LT -> x < y;
                case LE -> x <= y;
            };
            return Value.makeConstant(b? 1 : 0);
        }
        else{
            System.err.println("Unknown type in calculate");
            return Value.getNAC();
        }
    }
}
