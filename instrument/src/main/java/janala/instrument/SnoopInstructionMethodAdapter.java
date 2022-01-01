package janala.instrument;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import java.util.HashMap;
import java.util.LinkedList;

public class SnoopInstructionMethodAdapter extends MethodVisitor implements Opcodes {
  boolean isInit;
  boolean isSuperInitCalled; // Used to keep track of calls to super()/this() in <init>()
  int newStack = 0; // Used to keep-track of NEW instructions in <init>()
  LinkedList<TryCatchBlock> tryCatchBlocks;
  Label methodBeginLabel = new Label();
  Label methodEndLabel = new Label();

  private final String className;
  private final String methodName;
  private final String descriptor;
  private final String superName;

  private final GlobalStateForInstrumentation instrumentationState;

  public SnoopInstructionMethodAdapter(MethodVisitor mv, String className,
      String methodName, String descriptor, String superName,
      GlobalStateForInstrumentation instrumentationState) {
    super(ASM5, mv);
    this.isInit = methodName.equals("<init>");
    this.isSuperInitCalled = false;
    this.className = className;
    this.methodName = methodName;
    this.descriptor = descriptor;
    this.superName = superName;
    tryCatchBlocks = new LinkedList<>();

    this.instrumentationState = instrumentationState;
  }


  /** Push a value onto the stack. */
  private static void addBipushInsn(MethodVisitor mv, int val) {
    Utils.addBipushInsn(mv, val);
  }

  /** Add a GETVALUE call to synchronize the top stack with that of the symbolic stack. */
  private void addValueReadInsn(MethodVisitor mv, String desc, String methodNamePrefix) {
    Utils.addValueReadInsn(mv, desc, methodNamePrefix);
  }
  private void addInsn(MethodVisitor mv, String insn, int opcode) {
    addBipushInsn(mv, instrumentationState.incAndGetId());
    addBipushInsn(mv, lastLineNumber);
    mv.visitMethodInsn(INVOKESTATIC, Config.instance.analysisClass, insn, "(II)V", false);

    mv.visitInsn(opcode);
  }



  @Override
  public void visitMethodInsn(int opcode, String owner, String name, String desc, boolean itf) {


    if (opcode == INVOKESPECIAL && name.equals("<init>")) {


      // The first call to <init> within a constructor (`isInit`) on the same or super class,
      // which is not associated with a NEW instruction (`newStack` == 0),
      // will be considered as an invocation of super()/this().

      if (isInit && isSuperInitCalled == false && newStack == 0 &&
              (owner.equals(className) || owner.equals(superName))) {
        // Constructor calls to <init> method of the same or super class.
        //
        // XXX: This is a hack. We assume that if we see an <init> to same or
        // super class, then it must be a super() or this() call. However,
        // there are counter-examples such as `public Foo() { super(new Foo()); }`,
        // which will cause broken class files. This comment is here as a forewarning
        // for when this situation is eventually encountered due to a bytecode
        // verification error due to stack-map frames not matching up.
        //
        // In this case, we do not wrap the method call in try catch block as
        // it uses uninitialized this object.
        isSuperInitCalled = true;

        // Call <init>
        mv.visitMethodInsn(opcode, owner, name, desc, itf);

      } else {
        // Call to <init> but not a super() or this(). Must have occurred after a NEW.
        //addMethodWithTryCatch(opcode, owner, name, desc, itf);
        mv.visitMethodInsn(opcode, owner, name, desc, itf);

        // This is an outer constructor call, so reduce the NEW stack
        if (isInit) {
          newStack--;
          assert newStack >= 0;
        }
      }
    }
    else{
      mv.visitMethodInsn(opcode, owner, name, desc, itf);
    }
  }

  @Override
  public void visitCode() {
    super.visitCode();
    int iid = instrumentationState.incAndGetId();
    addBipushInsn(mv, iid);
    mv.visitInsn(ICONST_0);
    mv.visitMethodInsn(INVOKESTATIC, Config.instance.analysisClass, "LOGJUMP", "(II)V", false);
  }

  private void addConditionalJumpInstrumentation(int opcode, Label finalBranchTarget,
                                                 String instMethodName, String instMethodDesc) {
    int iid = instrumentationState.incAndGetId();
    instrumentationState.incAndGetId(); //reserver another counter for the other side of this branch

    Label intermediateBranchTarget = new Label();
    Label fallthrough = new Label();

    // Perform the original jump, but branch to intermediate label
    mv.visitJumpInsn(opcode, intermediateBranchTarget);
    // If we did not jump, skip to the fallthrough
    mv.visitJumpInsn(GOTO, fallthrough);

    // Now instrument the branch target
    mv.visitLabel(intermediateBranchTarget);
    //addValueReadInsn(mv, "Z", "GETVALUE_"); // Send value to logger (Z for boolean)
    //mv.visitInsn(POP);
    addBipushInsn(mv, iid);
    //addBipushInsn(mv, lastLineNumber);
    addBipushInsn(mv, 1); // Mark branch as taken
    //addBipushInsn(mv, getLabelNum(finalBranchTarget));
    mv.visitMethodInsn(INVOKESTATIC, Config.instance.analysisClass, instMethodName, instMethodDesc, false);
    mv.visitJumpInsn(GOTO, finalBranchTarget); // Go to actual branch target

    // Now instrument the fall through
    mv.visitLabel(fallthrough);
    //addValueReadInsn(mv, "Z", "GETVALUE_"); // Send value to logger (Z for boolean)
    //mv.visitInsn(POP);
    addBipushInsn(mv, iid);
    addBipushInsn(mv, 0); // Mark branch as not taken
    //addBipushInsn(mv, lastLineNumber);
    //addBipushInsn(mv, getLabelNum(finalBranchTarget));
    mv.visitMethodInsn(INVOKESTATIC, Config.instance.analysisClass, instMethodName, instMethodDesc, false);

    // continue with fall-through code visiting
  }

  @Override
  public void visitJumpInsn(int opcode, Label label) {
    if (isInit && !isSuperInitCalled) {
      // Jumps in a constructor before super() or this() mess up the analysis
      //throw new RuntimeException("Cannot handle jumps before super/this");
        mv.visitJumpInsn(opcode, label);
        return;
    }

    switch (opcode) {
      case IFEQ:
      case IFNE:
      case IFLT:
      case IFGE:
      case IFGT:
      case IFLE:
      case IF_ICMPEQ:
      case IF_ICMPNE:
      case IF_ICMPLT:
      case IF_ICMPGE:
      case IF_ICMPGT:
      case IF_ICMPLE:
      case IF_ACMPEQ:
      case IF_ACMPNE:
      case IFNULL:
      case IFNONNULL:
        addConditionalJumpInstrumentation(opcode, label,  "LOGJUMP", "(II)V");
        break;
      case GOTO:
        mv.visitJumpInsn(opcode, label);
        break;
      case JSR:
        mv.visitJumpInsn(opcode, label);
        break;
      default:
        throw new RuntimeException("Unknown jump opcode " + opcode);
    }
  }

  private Integer lastLineNumber = 0;

  @Override
  public void visitLineNumber(int lineNumber, Label label) {
    lastLineNumber = lineNumber;
    mv.visitLineNumber(lineNumber, label);
  }


  private int getLabelNum(Label label) {
    return System.identityHashCode(label);
  }


  @Override
  public void visitTableSwitchInsn(int min, int max, Label dflt, Label... labels) {
    // Save operand value
    //addValueReadInsn(mv, "I", "GETVALUE_");
    mv.visitInsn(Opcodes.DUP);
    // Log switch instruction
    addBipushInsn(mv, instrumentationState.incAndGetId());
    addBipushInsn(mv, min);
    addBipushInsn(mv, max);
    addBipushInsn(mv, getLabelNum(dflt));

    for (int i = 0; i < labels.length; i++) {
      //create a coverage probe for each of the arms, we'll refer to it by offset
      instrumentationState.incAndGetId();
    }


    //create a coverage probe for the default case
    instrumentationState.incAndGetId();
    mv.visitMethodInsn(INVOKESTATIC, Config.instance.analysisClass, "LOGTABLESWITCH", "(IIIII)V", false);
    mv.visitTableSwitchInsn(min, max, dflt, labels);
  }

  @Override
  public void visitLookupSwitchInsn(Label dflt, int[] keys, Label[] labels) {
    // Save operand value
    mv.visitInsn(Opcodes.DUP);

    // Log switch instruction
    addBipushInsn(mv, instrumentationState.incAndGetId());
    addBipushInsn(mv, getLabelNum(dflt));

    addBipushInsn(mv, keys.length);
    mv.visitIntInsn(NEWARRAY, T_INT);
    for (int i = 0; i < keys.length; i++) {
      mv.visitInsn(DUP);
      addBipushInsn(mv, i);
      addBipushInsn(mv, keys[i]);
      mv.visitInsn(IASTORE);
      //create a coverage probe for each of the arms, we'll refer to it by offset
      instrumentationState.incAndGetId();
    }


    //create a coverage probe for the default case
    instrumentationState.incAndGetId();
    mv.visitMethodInsn(INVOKESTATIC, Config.instance.analysisClass, "LOGLOOKUPSWITCH", "(III[I)V", false);
    mv.visitLookupSwitchInsn(dflt, keys, labels);
  }

  @Override
  public void visitMaxs(int maxStack, int maxLocals) {
    mv.visitMaxs(0, maxLocals);
  }

}
