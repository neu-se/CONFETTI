package edu.gmu.swe.knarr;

import edu.gmu.swe.knarr.internal.ConstraintSerializer;
import edu.gmu.swe.knarr.runtime.Coverage;
import edu.gmu.swe.knarr.runtime.StringUtils;
import org.apache.commons.io.input.CountingInputStream;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.ObjectIntHashMap;
import za.ac.sun.cs.green.expr.*;

import java.io.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class ConstraintDeserializer {


    private DataInputStream dis;
    private CountingInputStream countingInputStream;
    private IntObjectHashMap<Expression> referenceTable;
    private IntArrayList backReferencesRemaining;
    private int nextBackReference;

    public static void main(String[] args) throws Exception {
        File[] contents = new File("/Users/jon/Documents/NEU/Projects/jqf-artifact/").listFiles();
        for(File f: contents) {
            if(f.getName().endsWith(".ser")) {
                InputStream is = new BufferedInputStream(new FileInputStream(f));
                ConstraintDeserializer d = new ConstraintDeserializer();
                LinkedList<Expression> res = d.fromInputStream(is);
                System.out.println(f + ": " + res.size());
            }
        }
    }
    public LinkedList<Expression> fromInputStream(InputStream is) throws IOException {
        LinkedList<Expression> ret = new LinkedList<>();
        this.countingInputStream = new CountingInputStream(is);
        this.dis = new DataInputStream(this.countingInputStream);
        int nBackReferences = dis.readInt();
        this.nextBackReference = 0;
        backReferencesRemaining = new IntArrayList(nBackReferences);
        for (int i = 0; i < nBackReferences; i++) {
            backReferencesRemaining.add(dis.readInt());
        }
        if(backReferencesRemaining.size() == 0)
            this.nextBackReference = -1;
        backReferencesRemaining.sortThis();
        int size = dis.readInt();
        if(size > 0) {
            referenceTable = new IntObjectHashMap<>();
            missingReferenceHolders = new HashMap<>();
            countingInputStream.resetCount();
            int nConstraints = dis.readInt();
            for (int i = 0; i < nConstraints; i++) {
                ret.add(readExpression(null, null, 0));
            }
            if (countingInputStream.getCount() != size) {
                throw new StreamCorruptedException("Expected size " + size + " but read " + countingInputStream.getCount());
            }
        }
        return ret;
    }


    public LinkedList<Expression> fromBytes(byte[] buf, int offset, int len) throws IOException {
        return fromInputStream(new ByteArrayInputStream(buf, offset, len));
    }

    private HashMap<Integer, Expression> missingReferenceHolders = new HashMap<>();
    private Expression readTableReference(Expression referer, ReferringField field, int referringIdx) throws IOException {
        int ref = dis.readInt();
        Expression ret =  referenceTable.get(ref);
        if(ret == null)
            throw new NullPointerException("At " + ref);
        return ret;
    }

    int readingBackReferenceID = -1;

    private Expression readExpression(Expression referer, ReferringField referringField, int referringIdx) throws IOException {
        readingBackReferenceID = -1;
        if (nextBackReference >= 0 && this.countingInputStream.getCount() == this.backReferencesRemaining.get(nextBackReference)) {
            readingBackReferenceID = this.countingInputStream.getCount();
            nextBackReference++;
            if (nextBackReference >= this.backReferencesRemaining.size())
                nextBackReference = -1;
        }
        byte type = dis.readByte();
        switch(type){
            case ConstraintSerializer.T_TABLEREFERENCE:
                return readTableReference(referer, referringField, referringIdx);
            case ConstraintSerializer.T_ARRAYVARIABLE:
                return readArrayVariable();
            case ConstraintSerializer.T_BINARYOPERATION:
                return readBinaryOperation();
            case ConstraintSerializer.T_BOOLCONSTANT:
                return readBooleanConstant();
            case ConstraintSerializer.T_BVCONSTANT:
                return readBVConstant();
            case ConstraintSerializer.T_BVVARIABLE:
                return readBVVariable();
            case ConstraintSerializer.T_INTVARIABLE:
                return readIntVariable();
            case ConstraintSerializer.T_FUNCTIONCALL:
                return readFunctionCall();
            case ConstraintSerializer.T_INTCONSTANT:
                return readIntConstant();
            case ConstraintSerializer.T_NARYOPERATION:
                return readNaryOperation();
            case ConstraintSerializer.T_REALCONSTANT:
                return readRealConstant();
            case ConstraintSerializer.T_REALVARIABLE:
                return readRealVariable();
            case ConstraintSerializer.T_STRINGCONSTANT:
                return readStringConstant();
            case ConstraintSerializer.T_STRINGVARIABLE:
                return readStringVariable();
            case ConstraintSerializer.T_UNARYOPERATION:
                return readUnaryOperation();
            default:
                throw new IOException("Invalid object type: " + type);
        }
    }

    private IntVariable readIntVariable() throws IOException {
        IntVariable ret = new IntVariable();
        readVariableBase(ret);
        ret.lowerBound = dis.readInt();
        ret.upperBound = dis.readInt();
        return ret;
    }

    private BVVariable readBVVariable() throws IOException {
        BVVariable ret = new BVVariable();
        readVariableBase(ret);
        ret.size = dis.readInt();
        return ret;
    }

    private UnaryOperation readUnaryOperation() throws IOException {
        UnaryOperation ret = new UnaryOperation();
        readOperationBase(ret);
        ret.operand = readExpression(ret, ReferringField.UNARY_OPERAND, 0);
        return ret;
    }

    private StringVariable readStringVariable() throws IOException {
        StringVariable ret = new StringVariable();
        readVariableBase(ret);
        return ret;
    }

    private StringConstant readStringConstant() throws IOException {
        StringConstant ret = new StringConstant();
        readExpressionBase(ret);
        ret.value = dis.readUTF();
        return ret;
    }

    private RealVariable readRealVariable() throws IOException {
        RealVariable ret = new RealVariable();
        readVariableBase(ret);
        ret.lowerBound = dis.readDouble();
        ret.upperBound = dis.readDouble();
        return ret;
    }

    private RealConstant readRealConstant() throws IOException {
        RealConstant ret = new RealConstant();
        readExpressionBase(ret);
        ret.value = dis.readDouble();
        return ret;
    }

    private NaryOperation readNaryOperation() throws IOException {
        NaryOperation ret = new NaryOperation();
        readOperationBase(ret);
        ret.operands = new Expression[dis.readInt()];
        for(int i = 0 ; i < ret.operands.length; i++){
            ret.operands[i] = readExpression(ret, ReferringField.NARY_OPERAND, i);
        }
        return ret;
    }

    private IntConstant readIntConstant() throws IOException {
        IntConstant ret = new IntConstant();
        readExpressionBase(ret);
        ret.value = dis.readLong();
        return ret;
    }

    private FunctionCall readFunctionCall() throws IOException {
        FunctionCall ret = new FunctionCall();
        readExpressionBase(ret);
        ret.name = dis.readUTF();
        ret.arguments = new Expression[dis.readInt()];
        for(int i = 0; i < ret.arguments.length; i++){
            ret.arguments[i] = readExpression(ret, ReferringField.FUNCTION_CALL, i);
        }
        return ret;
    }

    private BVConstant readBVConstant() throws IOException {
        BVConstant ret = new BVConstant();
        readExpressionBase(ret);
        ret.size = dis.readInt();
        ret.value = dis.readLong();
        return ret;
    }

    private BoolConstant readBooleanConstant() throws IOException {
        BoolConstant ret = new BoolConstant();
        readExpressionBase(ret);
        ret.value = dis.readBoolean();
        return ret;
    }

    private BinaryOperation readBinaryOperation() throws IOException {
        BinaryOperation ret = new BinaryOperation();
        readOperationBase(ret);
        ret.left = readExpression(ret, ReferringField.BINARY_LEFT, 0);
        ret.right = readExpression(ret, ReferringField.BINARY_RIGHT, 0);
        return ret;
    }

    private ArrayVariable readArrayVariable() throws IOException {
        ArrayVariable ret = new ArrayVariable();
        readVariableBase(ret);
        switch(dis.readByte()){
            case 1:
                ret.type = Boolean.TYPE;
                break;
            case 2:
                ret.type = Byte.TYPE;
                break;
            case 3:
                ret.type = Short.TYPE;
                break;
            case 4:
                ret.type = Integer.TYPE;
                break;
            case 5:
                ret.type = Long.TYPE;
                break;
            case 6:
                ret.type = String.class; //We don't support anything other than the types above, so it doesn't really matter what we put here
                break;

        }
        return ret;
    }

    private void readExpressionBase(Expression expr) throws IOException {
        if(this.readingBackReferenceID >= 0){
            this.referenceTable.put(this.readingBackReferenceID, expr);
        }
        switch (dis.readByte()) {
            case ConstraintSerializer.METADATA_IS_NULL:
                expr.metadata = null;
                break;
            case ConstraintSerializer.METADATA_HASHSET_STRINGCOMPARISONS:
                int nComparisons = dis.readInt();
                HashSet<StringUtils.StringComparisonRecord> recs = new HashSet<>();
                for(int i = 0; i < nComparisons; i++){
                    String str = dis.readUTF();
                    StringUtils.StringComparisonType typ = comparisonTypes[dis.readByte()];
                    recs.add(new StringUtils.StringComparisonRecord(typ, str));
                }
                expr.metadata = recs;
                break;
            case ConstraintSerializer.METADATA_BRANCH_DATA:
                Coverage.BranchData d = new Coverage.BranchData();
                d.taken = dis.readBoolean();
                if (dis.readBoolean()) {
                    d.source = dis.readUTF();
                }
                d.takenCode = dis.readInt();
                d.notTakenCode = dis.readInt();
                d.notTakenPath = dis.readInt();
                d.breaksLoop = dis.readBoolean();
                expr.metadata = d;
                break;
            case ConstraintSerializer.METADATA_SWITCH_DATA:
                Coverage.SwitchData s = new Coverage.SwitchData();
                s.taken = dis.readBoolean();
                if (dis.readBoolean()) {
                    s.source = dis.readUTF();
                }
                s.switchID = dis.readInt();
                s.numArms = dis.readInt();
                s.arm = dis.readInt();
                break;
        }

    }
    private void readVariableBase(Variable expr) throws IOException{
        readExpressionBase(expr);
        expr.name = dis.readUTF();
    }

    static final StringUtils.StringComparisonType[] comparisonTypes = StringUtils.StringComparisonType.values();
    static final Operation.Operator[] operators = Operation.Operator.values();
    private void readOperationBase(Operation expr) throws IOException {
        readExpressionBase(expr);
        expr.operator = operators[dis.readShort()];
        switch(expr.operator){
            case I2BV:
            case SIGN_EXT:
            case ZERO_EXT:
                expr.immediate1 = dis.readInt();
                break;
            case EXTRACT:
                expr.immediate1 = dis.readInt();
                expr.immediate2 = dis.readInt();
                break;
        }
    }
    class PendingReference{
        Expression referer;
        ReferringField field;
        int idx;
        public PendingReference(Expression referer, ReferringField field, int idx) {
            this.referer = referer;
            this.field = field;
            this.idx = idx;
        }

    }
    static enum ReferringField{
        UNARY_OPERAND,
        NARY_OPERAND,
        BINARY_LEFT,
        BINARY_RIGHT,
        FUNCTION_CALL
    }
}
