theory paraGste imports Main Finite_Set
begin

section{*Variables and values*}

text{*
According to the aforementioned discussion in section ?, firstly we define the variables used in the protocols. 
There are two kinds of variables, global and parameterized (local) 
variables. In hardware implemetations of the protocols, 
the variables are implenteed as registers in global or local modules. *}

datatype varType=Ident  string | Para varType  nat |Field  varType   string 

datatype scalrValueType=enum string string |index nat | boolV bool | topVal | bottomVal

datatype inVar = Input varType   
  
datatype regVar= Reg varType

section{*Expressions and Formulas*}

datatype expType= IVar varType |
         Const scalrValueType |
         iteForm formula  expType  expType |
         uif string "expType list" |
         top |unKnown

and 
 formula = eqn expType expType|
           uip string "expType list" |
           andForm  formula formula |
           neg formula|
           orForm formula formula | 
           implyForm formula formula |
           chaos 



primrec down ::"nat \<Rightarrow>nat list" where
"down 0=[0]" |
"down (Suc n)=Suc n #(down n)"
 

text{*Similarly, a parameterized formula is a function from a parameter to a formula. We also define
 the $\mathsf{forall}$ and $mathsf{exists}$ formulas$.*}
type_synonym paraFormula="nat \<Rightarrow> formula"

fun forallForm::"nat list \<Rightarrow>paraFormula \<Rightarrow> formula" where
oneAllForm: "forallForm [i] forms = forms i"|
moreAllForm: "forallForm (i#j#xs)  forms = andForm (forms i) (forallForm (j#xs)  forms)"


fun existsForm::"nat list \<Rightarrow>paraFormula \<Rightarrow> formula" where
oneExForm: " existsForm [i] forms = forms i"|
moreExForm: " existsForm (i#j#xs)  forms = orForm (forms i) (forallForm (j#xs)  forms)"

type_synonym formulaExpPair="formula \<times>  expType"

fun caseExp::"formulaExpPair list  \<Rightarrow> expType" where
 "caseExp [gp] =iteForm (fst gp) (snd gp) unKnown"|
 "caseExp (gp # tls) =iteForm (fst gp) (snd gp) (caseExp tls )"
 
 

 
definition read::"varType \<Rightarrow> nat \<Rightarrow>expType \<Rightarrow>expType" where [simp]:
"read a bound e \<equiv> caseExp (map (\<lambda>i. ((eqn e (Const (index i))), IVar (Para a i))) (down bound))"

              
section{*assignment, statement, general statement*}
type_synonym assignType=  "varType \<times>   expType"

text{*A statement is is just a lists of assignments, but these assignments
 are extecuted in parallel, \emph{not} in a sequential order*}

datatype statement=  assign assignType         

primrec assignedVar::"statement \<Rightarrow>varType " where
"assignedVar (assign p) = (fst p)"

primrec assignedExp::"statement \<Rightarrow> expType" where
"assignedExp (assign p) = (snd p)"



text{*A parameterized statement is just a function from a parameter to a statement. 
For convenience, we also define the concatation of statements, and use it to define 
the $\mathsf{forall}$ statement.*}

type_synonym paraStatement= "nat \<Rightarrow> statement"

 


text{*A state transition from a state to another sate, which is caused by an execution of a statement, is
 defined as follows:*}

primrec statement2Assigns::"statement \<Rightarrow> assignType " where
"statement2Assigns (assign asgn)=asgn" 

primrec valOf::"assignType list \<Rightarrow> varType =>expType"  where
"valOf [] v=IVar v" |
"valOf (x#xs) v= (if ((fst x) =v) then (snd x) else valOf xs v)"

datatype generalizeStatement= Parallel "statement list"  |
   If formula generalizeStatement generalizeStatement



definition writeArr::"varType \<Rightarrow> nat \<Rightarrow>expType \<Rightarrow>expType\<Rightarrow>statement list" where
"writeArr a bound adre ce \<equiv> map  
   (\<lambda>i. assign ((Para a i), iteForm (eqn adre (Const (index i))) ce (IVar (Para a i))))
   (down bound)"

type_synonym formulaStatementPair ="formula \<times> generalizeStatement"

abbreviation skip::" generalizeStatement" where
"skip \<equiv> Parallel []"

primrec caseStatement::"formulaStatementPair list  \<Rightarrow> generalizeStatement" where
 "caseStatement [] = skip"|
 "caseStatement (gp # tls) =If (fst gp) (snd gp) (caseStatement tls )"

definition writeArr'::"varType \<Rightarrow> nat \<Rightarrow>expType \<Rightarrow>expType\<Rightarrow> generalizeStatement"  where [simp]:
"writeArr' a bound adre  ce\<equiv> caseStatement (map  (\<lambda>i. ((eqn adre (Const (index i))),Parallel [assign ((Para a i), ce)])) (down bound))"
 
(*primrec write'::"varType \<Rightarrow> nat \<Rightarrow>nat \<Rightarrow> expType \<Rightarrow>expType\<Rightarrow> generalizeStatement" where
"write' a bound 0 adre ce = ( bound = 0)  *)
 

text{*With the formalizatiion of formula and statement, it is natural to define a rule. A guard and
 statement of a rule are also defined for convenience. 
 
*}
 
section{*gste graph*} 
 
datatype node= Vertex nat

datatype  edge=Edge node  node 

type_synonym edgeToForm =  "edge \<Rightarrow>  formula"

datatype gsteSpec= Graph  node  "edge list" edgeToForm edgeToForm

primrec  antOf::"gsteSpec \<Rightarrow> edge \<Rightarrow> formula" where
"antOf  (Graph  init  edges ant conss) e = ant e"

primrec consOf::"gsteSpec \<Rightarrow>edge \<Rightarrow> formula" where
"consOf  (Graph  init  edges ant conss) e  = conss e"

primrec source::"edge \<Rightarrow> node" where
"source (Edge n1 n2) = n1"

primrec sink::"edge \<Rightarrow> node" where
"sink (Edge n1 n2) = n2"

primrec edgesOf ::"gsteSpec  \<Rightarrow>  edge set" where 
"edgesOf  (Graph  init  edges ant conss) = set edges   "

(*primrec nodes ::"gsteSpec  \<Rightarrow> node set" where 
"nodes (Graph  init  edges ant conss) = set ns"*) 

definition sourcesOf ::" edge set \<Rightarrow> node \<Rightarrow> node set" where
"sourcesOf es n =   {m.  Edge m n  \<in> es } " 

definition sinksOf ::"  edge set \<Rightarrow> node \<Rightarrow> node set" where
"sinksOf es m =   {n.  Edge m n \<in> es} " 

primrec initOf::"gsteSpec  \<Rightarrow> node" where
"initOf  (Graph  init  edges ant conss) = init"

fun  isPathOf::"node list \<Rightarrow> gsteSpec \<Rightarrow> bool" where
"isPathOf [] G=True" |
"isPathOf (n1#n2#ns) G = (  (Edge n1 n2) \<in>  (edgesOf G) \<and> isPathOf (n2#ns) G)" 

definition isGstePath::"node list \<Rightarrow> gsteSpec \<Rightarrow> bool" where
"isGstePath p G \<equiv> isPathOf p G \<and> 1< length p  \<and> p !0=initOf G"

primrec  isPathOf'::"edge list \<Rightarrow> gsteSpec \<Rightarrow> bool" where [simp]:
"isPathOf' [] G=True" | 
"isPathOf' (e#es) G = (( e \<in>  (edgesOf G) \<and> isPathOf' es G) \<and>(es=[]\<or> ( source (hd es))=(sink e)))" 




definition isGstePath'::"edge list \<Rightarrow> gsteSpec \<Rightarrow> bool" where [simp]:
"isGstePath' p G \<equiv>( p\<noteq>[]\<and>isPathOf' p G \<and>(source ( hd p))=initOf G)"

section{*semantics of a protocol*}
text{*A  state of a protocol  is an instantaneous snapshot of its  behaviour given by an assignment of  values to variables of
the circuit. Therefore, we define:*}

type_synonym state= "varType \<Rightarrow> scalrValueType "


datatype  circuit=Circuit "varType list" "varType list" "varType list" "statement list"  "statement list"

primrec outputFun::"circuit \<Rightarrow> statement list" where
"outputFun (Circuit inputs regs outs outf nf)  = outf"

primrec nextFun::"circuit \<Rightarrow> statement list" where
"nextFun (Circuit inputs regs outs outf nf) =nf"

primrec inputsOf::"circuit \<Rightarrow> varType set" where
"inputsOf (Circuit inputs regs outs outf nf) =set inputs"

primrec regsOf::"circuit \<Rightarrow> varType set" where
"regsOf (Circuit inputs regs outs outf nf) =set regs"

primrec outputsOf::"circuit \<Rightarrow> varType set" where
"outputsOf (Circuit inputs regs outs outf nf) =set inputs"


text{*Variables of a variable, an expression, a formula, and a statement is defined by
varsOfVar, varOfExp, varOfForm and varOfSent respectively*}

definition varsOfVar::" varType \<Rightarrow> varType set"  where  [simp]:
" varsOfVar x  = {x}" 


primrec varOfExp::"expType \<Rightarrow> varType set"  and
  varOfForm::"formula \<Rightarrow> varType set"  where 
"varOfExp  (IVar v) =   varsOfVar v" |
"varOfExp   (Const j) =  {}" |
"varOfExp   top={}"|
"varOfExp   unKnown={}"|
"varOfExp   (iteForm f e1 e2) =(varOfForm f) \<union>  (varOfExp   e1 )  \<union>   (varOfExp  e2)" |
"varOfExp   (uif f es) =    (Union (set (map varOfExp  es)))" |

"varOfForm   (eqn e1 e2) = ( (varOfExp   e1 )  \<union>   (varOfExp  e2))" |
"varOfForm   (uip p es) =    (Union (set (map varOfExp  es)))" |
"varOfForm   ( andForm f1 f2) =(  (varOfForm  f1 )  \<union>  (varOfForm  f2 ))"|
"varOfForm   (neg f1 ) = (  (varOfForm   f1 ))"|
"varOfForm   (orForm f1 f2) =(  (varOfForm   f1 )   \<union>   (varOfForm  f2 ))"|
"varOfForm   (implyForm f1 f2) = (  (varOfForm  f1 )  \<union>  (varOfForm f2 ))"|
"varOfForm   (chaos) ={}"



primrec  varOfSent::"statement \<Rightarrow> varType set" where
" varOfSent  (assign a)=( varsOfVar  (fst a)) "

primrec varOfGenStatement::"generalizeStatement \<Rightarrow> varType set" where
"varOfGenStatement (Parallel  SS)= \<Union> (set (map varOfSent SS))" |
"varOfGenStatement (If b S1 S2) =(varOfForm b) Un (varOfGenStatement S1) Un (varOfGenStatement S2)"


type_synonym scalrValueTypeListFun="scalrValueType list \<Rightarrow> scalrValueType"

type_synonym interpretFunType="string \<Rightarrow> scalrValueTypeListFun"

type_synonym scalrValueTypeListPred="scalrValueType list \<Rightarrow> bool"

type_synonym interpretPredType="string \<Rightarrow> scalrValueTypeListPred"

primrec scalar2Bool::"scalrValueType\<Rightarrow>bool" where
" scalar2Bool (boolV b) = b"

text{*The formal semantics of an expression and a formula is formalized as follows:*}
primrec expEval :: "interpretFunType \<Rightarrow> expType \<Rightarrow> state \<Rightarrow> scalrValueType" and 
 formEval :: "interpretFunType \<Rightarrow> formula \<Rightarrow> state \<Rightarrow>bool"  where
 
"expEval I  (IVar ie) s =  ( s ie)" |
"expEval I (Const i) s =  i"  |
"expEval I  (iteForm f e1 e2) s= 
   ( if (formEval I f s) then     (expEval I e1 s)
   else (expEval I e2 s))"  |
"expEval I top  s= topVal"|
"expEval I unKnown s=bottomVal" |
"expEval I  (uif f es)  s=   (I f) (map (\<lambda> e. expEval  I e s) es) " |

evalExp: "formEval I (eqn e1 e2) s= ((expEval I e1 s) = (expEval I e2 s))" |
"formEval I  (uip p es)  s=    scalar2Bool ( (I p) (map (\<lambda> e. expEval  I e s) es)) " |
evalAnd: "formEval I ( andForm f1 f2) s=( (formEval I f1 s) \<and> (formEval I f2 s))"|
evalNeg: "formEval I (neg f1 ) s= ( \<not>(formEval I f1 s))"|
evalOr: "formEval I (orForm f1 f2) s=( (formEval I f1 s) \<or>  (formEval I f2 s))"|
evalImp:"formEval I (implyForm f1 f2) s= ( (formEval I f1 s) \<longrightarrow>  (formEval I f2 s))" |
"formEval I chaos s=True"

fun sqSatAssert::"interpretFunType \<Rightarrow>state list \<Rightarrow> edge list\<Rightarrow>edgeToForm \<Rightarrow> bool" where [simp]:
"sqSatAssert I [] es assert = True"|
"sqSatAssert I sq [] assert = True"|
"sqSatAssert I (s#sq) (e#es) assert= ((sqSatAssert I sq es assert) \<and> formEval I (assert e) s)"



definition wellformedAssgnList::"assignType list => bool" where
" wellformedAssgnList asgns\<equiv>distinct (map fst asgns)"


  
primrec transAux:: "assignType list \<Rightarrow>interpretFunType \<Rightarrow> state \<Rightarrow>state " where
"transAux [] I s= s " |
"transAux (pair#asgns) I s=( transAux asgns I s) ((fst pair):= expEval I (snd pair) s) "

definition trans:: "statement list\<Rightarrow> interpretFunType \<Rightarrow> state \<Rightarrow>state " where [simp]:
"trans S I s \<equiv> transAux (map statement2Assigns S) I s"

primrec genTrans::"generalizeStatement\<Rightarrow> interpretFunType  \<Rightarrow> state \<Rightarrow>state " where 
"genTrans (Parallel S) I s = trans S I s" |
"genTrans (If b S1 S2) I s=(if (formEval I b s) then (genTrans  S1 I s) else  (genTrans S2 I s))"


datatype  circuit1=Circuit1 "varType list" "varType list"  "generalizeStatement"  



primrec nextFun1::"circuit1 \<Rightarrow> generalizeStatement " where
"nextFun1 (Circuit1 inputs regs  nf) =nf"

primrec inputsOf1::"circuit1 \<Rightarrow> varType set" where
"inputsOf1 (Circuit1 inputs regs nf) =set inputs"

primrec regsOf1::"circuit1 \<Rightarrow> varType set" where
"regsOf1 (Circuit1 inputs regs  nf) =set regs"

primrec wellGenStatement::"generalizeStatement \<Rightarrow> bool" where
"wellGenStatement (Parallel S) = wellformedAssgnList (map statement2Assigns S)"  |
"wellGenStatement (If b S1 S2) = ((wellGenStatement S1) \<and> (wellGenStatement S2))"


definition transOfCircuit1::"circuit1 \<Rightarrow>interpretFunType \<Rightarrow>state \<Rightarrow>state " where [simp]:
"transOfCircuit1 M I s  \<equiv> (genTrans (nextFun1 M) I s)"

fun istrajOfCircuit1::"circuit1 \<Rightarrow> interpretFunType \<Rightarrow> state list \<Rightarrow> bool" where [simp]:
"istrajOfCircuit1 M I [] = True"|
"istrajOfCircuit1 M I [s] = True" |
"istrajOfCircuit1 M I (s#s'#sq) =(   s'=transOfCircuit1 M I  s \<and>istrajOfCircuit1 M I (s'#sq))"


definition circuitSatGsteSpec1::"circuit1 \<Rightarrow> gsteSpec \<Rightarrow>  interpretFunType \<Rightarrow>bool" where
"circuitSatGsteSpec1 M G I\<equiv> \<forall> p sq. istrajOfCircuit1 M I sq \<longrightarrow> isGstePath' p G
  \<longrightarrow> sqSatAssert I sq p (antOf G) \<longrightarrow>   sqSatAssert I sq p (consOf G)"
  
type_synonym nodeTagFunc="node \<Rightarrow> formula"
  
definition consistent1::"circuit1 \<Rightarrow> interpretFunType  \<Rightarrow> gsteSpec \<Rightarrow> nodeTagFunc \<Rightarrow> bool" where
"consistent1 M I G tag \<equiv>( \<forall>e s s'. 
  (e \<in> edgesOf G \<longrightarrow> formEval I (antOf G e)  s \<longrightarrow>
  s'=transOfCircuit1 M I s \<longrightarrow> formEval I (tag (source e))  s \<longrightarrow> formEval I (tag (sink e))  s')) \<and>
  (\<forall>e s . (formEval I (tag (source e))  s) \<longrightarrow> formEval I (antOf G e)  s \<longrightarrow>   formEval I (consOf G e)  s)"

section{*substitution, weakest precondition*}

primrec substExp :: "expType\<Rightarrow> assignType list \<Rightarrow>expType"  and 
substForm ::"formula \<Rightarrow> assignType list \<Rightarrow> formula" where 

substExpVar: "substExp  (IVar v') asgns=   (valOf  asgns v')  "| 

substExpConst: "substExp  (Const i)  asgns= Const i" |

substTop: "substExp top asgns=top" |

substUnkown: "substExp unKnown asgns=unKnown" |

substExpite: "substExp  (iteForm f e1 e2)  asgns= (iteForm (substForm f asgns) (substExp e1  asgns) (substExp e2  asgns))"|

substUif: "substExp (uif f es) asgns =( uif f (map (\<lambda>e. substExp e asgns) es))"| 

"substForm (eqn l r)  asgns=(eqn (substExp l  asgns) (substExp r  asgns))"  |
"substForm ( andForm f1 f2)  asgns =   ( andForm (substForm f1  asgns)  (substForm f2  asgns))"|
"substForm (neg f1 )   asgns= (neg ( substForm f1  asgns ))"|
"substForm (orForm f1 f2)   asgns= ( orForm (substForm f1  asgns )  (substForm f2  asgns))"|
"substForm (implyForm f1 f2)   asgns= (implyForm (substForm f1 asgns)  (substForm f2  asgns))" |
"substForm (uip p es)   asgns= ( uip p (map (\<lambda>e. substExp e asgns) es))" |
"substForm  chaos   asgns=chaos"



primrec  preCond1 ::" formula \<Rightarrow> generalizeStatement  \<Rightarrow>formula" where
preCondSimp1:"preCond1 f (Parallel S)  = substForm f (map statement2Assigns S) " |
preCondSimp2:"preCond1 f  (If b S1 S2) = andForm (implyForm b (preCond1 f  S1)) (implyForm (neg b) (preCond1 f  S2))"

primrec  preExp1 ::" expType \<Rightarrow>  generalizeStatement  \<Rightarrow>expType" where 
preExpSimp1: "preExp1 e  (Parallel S)  = substExp e (map statement2Assigns S)  " |
preExpSimp2:"preExp1 e   (If b S1 S2) = iteForm b (preExp1 e S1) (preExp1 e S2)"




lemma lemmaOnValOf:
  
  shows "expEval I (preExp1 (IVar v) nf) s = genTrans nf I s v" 
  (is "?LHS1 nf =?RHS1 nf ")
proof(induct_tac nf)
  fix x
  let ?nf="Parallel x"
  show "?LHS1 ?nf=?RHS1 ?nf"
  proof(auto)
  show "expEval I (valOf (map statement2Assigns x) v) s = transAux (map statement2Assigns x) I  s v"
     (is "?LHS2 x =?RHS2 x ")
  proof(induct_tac x)
  show "?LHS2 [] =?RHS2 []"
       by auto
    next
  fix a nf
  assume b1:"?LHS2 nf =?RHS2 nf"
  let ?nf="a#nf"
  show "?LHS2 ?nf =?RHS2 ?nf"
  apply(cut_tac b1,simp) done
  qed
  qed
next
  fix b S1 S2
  assume b1:" expEval I (preExp1 (IVar v) S1) s = genTrans S1 I s v" and
  b2:" expEval I (preExp1 (IVar v) S2) s = genTrans S2 I s v" 
  let ?nf="If b S1 S2"
  show "?LHS1 ?nf=?RHS1 ?nf"
 proof(case_tac "formEval I b s")
  assume c:"formEval I b s"
  show "?LHS1 ?nf=?RHS1 ?nf" by(cut_tac b1 c, auto)
  next
  assume c:"\<not> formEval I b s"
  show "?LHS1 ?nf=?RHS1 ?nf" by(cut_tac b2 c, auto)
  qed
qed

lemma itePreExp1:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (genTrans  nf I s)  
   \<longrightarrow> expEval I (preExp1 x2 nf) s = expEval I x2 (genTrans  nf I s)
   \<longrightarrow>  expEval I (preExp1 x3 nf) s = expEval I x3 (genTrans  nf I s)
   \<longrightarrow>   expEval I (preExp1 (iteForm x1 x2 x3) nf) s = expEval I (iteForm x1 x2 x3) (genTrans  nf I s)"
   (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?p3 nf\<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?p3 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1 \<longrightarrow>?p2 S1 \<longrightarrow>?p3 S1 \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2 \<longrightarrow>?p2 S2 \<longrightarrow>?p3 S2 \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?p3 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?p3 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?p3 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed

lemma eqPre:
  "expEval I (preExp1 x1 nf) s = expEval I x1 (genTrans nf I s)\<longrightarrow>
   expEval I (preExp1 x2 nf) s = expEval I x2 (genTrans nf I s)\<longrightarrow>
   formEval I (preCond1 (eqn x1 x2) nf) s = formEval I (eqn x1 x2) (genTrans nf I s)"
   (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1 \<longrightarrow>?p2 S1  \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2 \<longrightarrow>?p2 S2  \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed  

lemma auxOnufiPre: "(\<forall>x2a. x2a \<in> set es \<longrightarrow> expEval I (preExp1 x2a (Parallel S)) s = expEval I x2a (genTrans (Parallel S) I s)) \<longrightarrow>
 (map ((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e (map statement2Assigns S))) es) =
      (map (\<lambda>e. expEval I e (transAux (map statement2Assigns S) I s)) es)" (is "?P es")
proof(induct_tac es)
  let ?nf="Parallel S"
  show "?P []" by auto
  next 
  fix x xs
  assume b1:"?P xs"
  show "?P (x#xs)" (is "?P1 (x#xs) \<longrightarrow> ?P2 (x#xs)")
  proof 
  assume c1:"?P1 (x#xs)"
  have b2:"?P1 xs" by (cut_tac c1,auto )
  then have b3:"?P2 xs" by(cut_tac b1,auto)
  
    
   have b5:"((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e (map statement2Assigns S))) x =
  (\<lambda>e. expEval I e (transAux (map statement2Assigns S) I s)) x" 
    by (cut_tac c1,simp) 
  
  show "?P2 (x#xs)" (is "?LHS (x#xs) = ?RHS (x#xs)")
  by(cut_tac b5 b3, auto)
  qed
qed

lemma uifPre:  

" (\<forall>x2a. x2a \<in> set es \<longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (genTrans nf I s)) \<longrightarrow>
             expEval I (preExp1 (uif f es) nf) s = expEval I (uif f es) (genTrans nf I s)   "   
           (  is "?p1 nf\<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   
   show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   proof 
   assume a1:"?p1 ?nf"
   have b1:"(map ((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e (map statement2Assigns S))) es) =
      (map (\<lambda>e. expEval I e (transAux (map statement2Assigns S) I s)) es)"
      using a1 by auto
   
      
   then show "?LHS ?nf=?RHS ?nf" apply simp
   apply( simp add:b1)
   done
   qed
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1   \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2   \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf   \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf   \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed  

lemma uipPre:  

" (\<forall>x2a. x2a \<in> set es \<longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (genTrans nf I s)) \<longrightarrow>
             formEval I (preCond1 (uip pn es) nf) s =formEval I (uip pn es) (genTrans nf I s)   "   
           (  is "?p1 nf\<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   
   show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   proof 
   assume a1:"?p1 ?nf"
   have b1:"(map ((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e (map statement2Assigns S))) es) =
      (map (\<lambda>e. expEval I e (transAux (map statement2Assigns S) I s)) es)"
      using a1 by auto
   
      
   then show "?LHS ?nf=?RHS ?nf" apply simp
   apply( simp add:b1)
   done
   qed
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1   \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2   \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf   \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf   \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed  

lemma andPre:       
  "formEval I (preCond1 x1 nf) s = formEval I x1 (genTrans nf I s) \<longrightarrow>
   formEval I (preCond1 x2 nf) s = formEval I x2 (genTrans nf I s) \<longrightarrow>
   formEval I (preCond1 (andForm x1 x2) nf) s = formEval I (andForm x1 x2) (genTrans nf I s)"    
    (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1 \<longrightarrow>?p2 S1  \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2 \<longrightarrow>?p2 S2  \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed        

lemma orPre:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (genTrans nf I s) \<longrightarrow>
   formEval I (preCond1 x2 nf) s = formEval I x2 (genTrans nf I s) \<longrightarrow>
   formEval I (preCond1 (orForm x1 x2) nf) s = formEval I (orForm x1 x2) (genTrans nf I s)"    
    (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1 \<longrightarrow>?p2 S1  \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2 \<longrightarrow>?p2 S2  \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed      

lemma implyPre:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (genTrans nf I s) \<longrightarrow>
   formEval I (preCond1 x2 nf) s = formEval I x2 (genTrans nf I s) \<longrightarrow>
   formEval I (preCond1 (implyForm x1 x2) nf) s = formEval I (implyForm x1 x2) (genTrans nf I s)"    
    (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1 \<longrightarrow>?p2 S1  \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2 \<longrightarrow>?p2 S2  \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed    

lemma notPre:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (genTrans nf I s) \<longrightarrow>
   formEval I (preCond1 (neg x1 ) nf) s = formEval I (neg x1 ) (genTrans nf I s)"    
    (is "?p1 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="Parallel S"
   show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto
next
  fix b S1 S2 
  let ?nf="If b S1 S2"
  assume b1:"?p1 S1 \<longrightarrow>?LHS S1=?RHS S1" and 
  b2: "?p1 S2  \<longrightarrow>?LHS S2=?RHS S2"
  show "?p1 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
  proof(case_tac "formEval I b s")
    assume c:"formEval I b s"
    show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b1 c,auto)
    next
    assume c:"\<not> formEval I b s"
    show "?p1 ?nf   \<longrightarrow>?LHS ?nf=?RHS ?nf"
    by (cut_tac b2 c,auto)
  qed
qed       

lemma lemmaOnPre:
  
  shows "(expEval I (preExp1 e nf) s =   expEval I  e (genTrans nf I s)) \<and>
   (formEval I (preCond1 f nf) s = formEval I f (genTrans nf I s))"
   (is "((  ?LHS e =?RHS e )\<and> ( ?LHS1 f =?RHS1 f ))")      
proof(induct_tac e and f)
  fix v
  let ?e="(IVar v)"
  show  "  ?LHS ?e =?RHS ?e "
  apply(simp)
  using  lemmaOnValOf by blast 
 
next
  fix n
  let ?e="(Const n)"
  show  "?LHS ?e =?RHS ?e "
  proof(induct_tac nf,auto)qed
       
next
  fix f e1 e2
  assume b1:"( ?LHS1 f =?RHS1 f )" and
  b2:"?LHS e1 =?RHS e1 " and a3:"?LHS e2 =?RHS e2 "
  let ?e="iteForm f e1 e2"
  show "?LHS ?e =?RHS ?e " (is "?LHS1 nf=?RHS1 nf")
  by (simp add: a3 b1 b2 itePreExp1)
  
next
  let ?e="top"
  show "?LHS ?e =?RHS ?e "
  proof(induct_tac nf,auto)qed
next
  let ?e="unKnown"
  show "?LHS ?e =?RHS ?e "
  proof(induct_tac nf,auto)qed 
next
  fix e1 e2
  assume a1:" ?LHS e1 =?RHS e1 " and a2:" ?LHS e2 =?RHS e2 "
  let ?f="eqn e1 e2"
  show "(?LHS1 ?f =?RHS1 ?f )"
  by (simp add: a1 a2 eqPre) 
  
next
  fix f1 f2
  assume a1:" ( ?LHS1 f1 =?RHS1 f1 )" and  a2:"  ?LHS1 f2 =?RHS1 f2 "
  let ?f="andForm f1 f2"
  show "( ?LHS1 ?f =?RHS1 ?f )"
  by (simp add: a1 a2 andPre)
  
next
  fix f1
  assume a1:" (?LHS1 f1 =?RHS1 f1 )"
  let ?f="neg f1"
  show "( ?LHS1 ?f =?RHS1 ?f )"
  by (simp add: a1  notPre)
next   
  fix f1 f2
  assume a1:" ( ?LHS1 f1 =?RHS1 f1 )" and  a2:" ?LHS1 f2 =?RHS1 f2 "
  let ?f="implyForm f1 f2"
  
  show "(?LHS1 ?f =?RHS1 ?f )"
  by (simp add: a1 a2 implyPre)
next
 
  fix f1 f2
  assume a1:" ( ?LHS1 f1 =?RHS1 f1 )" and  a2:" ( ?LHS1 f2 =?RHS1 f2 )"
  let ?f="orForm f1 f2"
  
  show "(?LHS1 ?f =?RHS1 ?f )"
   by (simp add: a1 a2 orPre)
next
  let ?f="chaos"
  show "( ?LHS1 ?f =?RHS1 ?f )"
  proof(induct_tac nf,auto)qed
next
  fix fn es
  let ?e="uif fn es"
  assume a1:"(\<And>x2a. x2a \<in> set es \<Longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (genTrans nf I s))"
   show "?LHS ?e =?RHS ?e " (is "?LHS1 nf=?RHS1 nf")
   by (simp add: a1 uifPre)
next
  fix pn es
  let ?f="uip pn es"
  assume a1:"(\<And>x2a. x2a \<in> set es \<Longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (genTrans nf I s))"
   show "?LHS1 ?f =?RHS1 ?f "  
   by (simp add: a1 uipPre)
qed

lemma lemmaOnPreExp:  
shows "expEval I (preExp1 e nf) s =   expEval I e (genTrans nf I s) "
  by (simp add: lemmaOnPre)

lemma lemmaOnPreForm:  
shows "formEval I (preCond1 f nf) s = formEval I f (genTrans nf I s)"
  by (simp add: lemmaOnPre)
(*lemma lemmaOnPreCond:
  assumes a1:"wellDefinedCircuit1 M" and a2:"M=Circuit1 inputs regs   nf" and
  a3:"(varOfForm f) \<subseteq> (regsOf1 M)" and a4:"formEval (preCond1 f M) s "
  shows "  (( formEval f (transOfCircuit1 M s))) "
  using a4 a1 a2 a3 lemmaOnPre by blast*)

section{*main lemma: consistency lemma*}
  
definition tautlogy::"formula \<Rightarrow>  interpretFunType \<Rightarrow>    bool" where [simp]:
"tautlogy f I \<equiv> \<forall>s. formEval I f s"

primrec andListForm::"formula list \<Rightarrow> formula " where
"andListForm [] = chaos" |
"andListForm  (f#fs) = andForm f (andListForm  fs)"

lemma andList1Aux:
   shows "formEval I ( (andListForm frms)) s  \<longrightarrow> frm \<in>set frms \<longrightarrow> formEval I ( frm) s "
   proof(induct_tac frms,auto)qed
   
lemma andList1:
   shows "formEval I ( (andListForm frms)) s  \<Longrightarrow>  frm \<in>set frms \<Longrightarrow> formEval I ( frm) s " 
    by (metis andList1Aux)


type_synonym nodeTagFuncList="node \<Rightarrow> formula list"

 
definition consistent'::"circuit1 \<Rightarrow> interpretFunType \<Rightarrow> gsteSpec \<Rightarrow> nodeTagFuncList \<Rightarrow> bool" where [simp]:
"consistent' M I G tag \<equiv>( \<forall>e. 
  (e \<in> edgesOf G \<longrightarrow> 
  (let f=andListForm (tag (sink e)) in 
   let f' =andListForm  (tag (source e)) in
  tautlogy (implyForm (andForm f' (antOf G e)) (preCond1 f  (nextFun1 M))) I )))"

(*definition consistentInst::" gsteSpec \<Rightarrow> nodeTagFuncList \<Rightarrow> bool" where [simp]:
"consistentInst  G tag \<equiv>( \<forall>e. 
  (e \<in> edgesOf G \<longrightarrow> 
  (let f=andListForm (tag (source e)) in
  (tautlogy (implyForm (andForm f (antOf G e)) (consOf G e))))))"*)

fun sqSatTagFunc::"state list \<Rightarrow> interpretFunType\<Rightarrow> edge list\<Rightarrow>nodeTagFuncList\<Rightarrow> bool" where [simp]:
"sqSatTagFunc [] I [] tag = True"|
"sqSatTagFunc (s#sq) I [] tag = False"|
"sqSatTagFunc [] I (e#es) tag = False"|
"sqSatTagFunc (s#sq) I (e#es) tag= 
       ((sqSatTagFunc sq I es tag) \<and> formEval I (andListForm (tag (source e)))  s
       )"

lemma sqSatConsisitentGraph:
  assumes a1:"consistent' M I G tag" and   a2:"wellDefinedCircuit1 M" 
  and a3:"M=Circuit1 inputs regs   nf"  
  shows "e \<in> edgesOf G \<longrightarrow>(varOfForm (andListForm (tag (sink e)))) \<subseteq> (regsOf1 M)\<longrightarrow>
  formEval I (andListForm (tag (source e))) s\<longrightarrow> formEval I(antOf G e) s \<longrightarrow>
  formEval I (andListForm (tag (sink e))) (genTrans nf I s)"
  proof(rule impI)+
   assume b1:"e \<in> edgesOf G" and b2:"formEval I (andListForm (tag (source e))) s" and
   b3:" formEval I (antOf G e) s"  and b4:"(varOfForm (andListForm (tag (sink e)))) \<subseteq> (regsOf1 M)"
   let ?f="andListForm (tag (sink e))"
   have b5:"formEval I (preCond1 ?f  nf) s"
   proof -
    from a1 b1  have b4:"(let f=andListForm (tag (sink e)) in 
    let f' =andListForm  (tag (source e)) in
    tautlogy (implyForm (andForm f' (antOf G e)) (preCond1 f  (nextFun1 M))) I )"
    by (metis a3 consistent'_def nextFun1.simps)
    then show b5:"formEval I (preCond1 ?f  nf) s" 
    by(cut_tac a3 b3 b2, auto)
  qed
  show "formEval I (andListForm (tag (sink e))) (genTrans nf I s)"
  using a2 a3 b4 b5 lemmaOnPre by blast
 qed

definition stateSpec::"circuit1 \<Rightarrow> gsteSpec\<Rightarrow>nodeTagFuncList \<Rightarrow> bool" where [simp]:
"stateSpec M G tag \<equiv>\<forall> e. e \<in>edgesOf G \<longrightarrow> (varOfForm (andListForm (tag (sink e)))) \<subseteq> (regsOf1 M)"
 
lemma consistentLemma:
  assumes a1:"consistent' M I G tag" and   a2:"wellDefinedCircuit1 M" 
  and a3:"M=Circuit1 inputs regs   nf" and a4:"stateSpec M G tag"
  shows a1:"\<forall>sq. ((\<not>( p=[]) \<longrightarrow>
  formEval I (andListForm (tag (source (hd p)))) (hd sq))\<longrightarrow> (length p= length sq)\<longrightarrow>
  istrajOfCircuit1 M I sq \<longrightarrow> isPathOf' p G \<longrightarrow> sqSatAssert I  sq p (antOf G)\<longrightarrow>
  sqSatTagFunc sq I p tag  )" (is " ?P p")
proof(induct_tac p)
  show "?P []" 
  apply(rule allI,(rule impI)+,simp) done
next
  fix e p
  assume b1:"?P p"
  let ?p="e # p"
  show "?P ?p"
  proof(rule allI,(rule impI)+)
    fix sq
    assume c1:"e # p \<noteq> [] \<longrightarrow> formEval I (andListForm (tag (source (hd (e # p))))) (hd sq)"
    and c2:"length (e # p) = length sq" and c3:" istrajOfCircuit1 M I sq" and c4:"isPathOf' (e # p) G "
    and c4a:"sqSatAssert I sq ?p (antOf G)"
    have "\<exists> s sq'. sq=s#sq' \<and> length p=length sq'" 
    apply(cut_tac c2,simp)
    by (metis Suc_length_conv)
    then obtain s and sq' where c5:" sq=s#sq'\<and> length p=length sq'" by blast
    have c6:"formEval I (andListForm (tag (source e))) s"
    using c1 c5 by auto
    show "sqSatTagFunc   sq I (e # p) tag"
    proof(cut_tac c5,simp,rule conjI)
      have "sq'=[] \<or> (\<exists> s' sq''. sq'=s'#sq'')" 
        apply(case_tac sq', auto) done
      moreover
      {assume d1:"sq'=[]"
        have d2:"p=[]"
        using c5 d1 by auto 
        have " sqSatTagFunc sq' I p tag"
          by(cut_tac d1 d2, simp)
      }
      moreover
      {assume d1:"(\<exists> s' sq''. sq'=s'#sq'')"
       then obtain s' sq'' where d1:"sq'=s'#sq''" by blast
       with c5 have "\<exists>e' p'. p=e' # p'" 
       apply simp
       by (metis Suc_length_conv)
       then obtain e' p' where d2:"p= e' #p'" by blast
       have d3:"p \<noteq> []" using d2 by simp
       have d4:"istrajOfCircuit1 M I sq'" using c3 c5 d1 by auto
       have d5:"s'=(transOfCircuit1 M I s)" using c3 c5 d1 by auto
       have d6:"sqSatAssert I  sq'  p (antOf G)" using c4a c5 apply auto done
       have d7:" formEval I (antOf G e) s" using c4a c5 apply auto done
       have d8:" e \<in> edgesOf G" using c4 by auto
       have d9:"(varOfForm (andListForm (tag (sink e)))) \<subseteq> (regsOf1 M)" using a4 d8 by auto
       have d10:"formEval I  (andListForm (tag (sink e))) (genTrans nf I s)"
       using a1 a2 a3 c6 d7 d8 d9 sqSatConsisitentGraph by blast 
       have d11:"source (hd p) = sink e" using c5 d2 c4 by auto
       have d12:"(transOfCircuit1 M I s) =(hd sq')" using c3 d1 c5 apply auto done
       have d13:"formEval I (andListForm (tag (source (hd p)))) (hd sq') "
       using a3 d10 d11 d12 by auto 
       have d14:"isPathOf' p G" using c4 by auto
       have d15:"sqSatTagFunc sq' I p tag" using b1 d3 d13 d4 c4 c5 d14 d6 by auto
       }
      ultimately show "sqSatTagFunc sq' I p tag" by auto
    next
      show "formEval I (andListForm (tag (source e))) s" using c6 by auto
  qed
 qed
qed


section{*miscellaneous definitions and lemmas*}


lemma varsOfSent1:
  shows " varOfGenStatement (Parallel  SS) = set (map fst (map statement2Assigns SS))" (is "?P SS")
  proof(induct_tac SS) 
  show "?P []" by auto 
  fix a list
  assume b1:"?P list"
  have "\<exists> x v. a=assign (x,v)" by(case_tac a,auto)
  then obtain x v where b2:"a=assign (x,v)" by auto
  show "?P (a#list)"
  proof(cut_tac b1 b2,auto) qed
qed 



lemma simpDown:"down 5=[5,4,3,2,1,0]"
 by (simp add: eval_nat_numeral(2) eval_nat_numeral(3))

lemma downNIsNotEmpty:
  "\<exists> j xs. down N= j#xs" (is "?P N")
  proof(induct_tac N,auto)qed   




 
 

text{*definitions and lemmas on forallForm formula constructor*}  

lemma forall1:
  shows "\<forall> i. i \<le> N \<longrightarrow>formEval I (forallForm (down N) pf ) s\<longrightarrow>formEval I (pf i) s" (is "?P N")  
proof(induct_tac N)
    show "?P  0"
      by simp
  next
    fix N
    assume b1:"?P N"
    show "?P  (Suc N)"
      proof(case_tac "N =0")
        assume c1:"N=0"
        show "?P  (Suc N)"
        proof(cut_tac c1, auto,case_tac "i=0", auto,case_tac "i=1",auto)qed
      next
        assume c1:"N\<noteq>0"
        have "0<N " 
          by(cut_tac c1, arith)
       then have c2:"\<exists> N'. down (Suc N)=(Suc N)#N#down N'"
         by (metis down.simps(2) gr0_conv_Suc)
       then obtain N' where c2:"down (Suc N)=(Suc N)#N#down N'"
         by blast
       then have c3:"(N#down N')=down N"
         by simp
       show "?P  (Suc N)"      
       proof(rule allI,(rule impI)+,cut_tac c2,simp)
         fix i
         assume d1:"i\<le> Suc N" and d2:" formEval I (pf (Suc N)) s \<and> formEval I (forallForm (N # down N') pf) s"
         have "i=Suc N \<or> i<Suc N" 
           by (cut_tac d1, arith)
         moreover
         {assume e1:"i=Suc N"
           have " formEval I (pf i) s"
             by (metis (lifting) d2 e1)
         }
         moreover
         {assume e1:"i<Suc N"           
           have " formEval I (pf i) s"
             by (metis b1 c3 d1 d2 le_Suc_eq)
         }
         ultimately show "formEval I (pf i) s"
           by blast
       qed
     qed
   qed

lemma forallLemma [simp,dest]:
  assumes a1:"i \<le> N" and a2:"formEval I (forallForm (down N) pf ) s"
  shows "formEval I (pf i) s"
by (metis a1 a2 forall1)      

subsection{*lemmas on varsOf*}  

fun  cat::"generalizeStatement \<Rightarrow> generalizeStatement  \<Rightarrow>generalizeStatement " where  
cat1:"cat  (Parallel S) (Parallel S') = Parallel (S@S')" 

text{*For conveniece, we also define the concatation of statements.*}

fun parallelList::"generalizeStatement list \<Rightarrow> generalizeStatement" where
"parallelList [S] = S"|
"parallelList (S1#SL) = cat S1 (parallelList (SL))" 

abbreviation rst::"expType" where
"rst \<equiv> IVar (Ident ''rst'')"

abbreviation push::"expType" where
"push \<equiv> IVar (Ident ''push'')"

abbreviation pop::"expType" where
"pop \<equiv> IVar (Ident ''pop'')"

abbreviation dataIn::"expType" where
"dataIn \<equiv> IVar (Ident ''dataIn'' )"



abbreviation LOW::"expType" where
"LOW \<equiv> Const (index 0)"
abbreviation HIGH::"expType" where
" HIGH \<equiv> Const (index 1)"

abbreviation emptyFifo::"expType" where
" emptyFifo \<equiv> IVar (Ident ''empty'' ) "

abbreviation tail::"expType" where
" tail \<equiv> IVar (Ident ''tail'' ) "

abbreviation head::"expType" where
" head \<equiv> IVar (Ident ''head'' ) "


abbreviation full::"expType" where
" full \<equiv> IVar (Ident ''full'' ) "

abbreviation fullForm::"nat\<Rightarrow>formula" where
" fullForm DEPTH\<equiv> eqn tail (Const (index DEPTH)) "

abbreviation mem::"nat \<Rightarrow> expType" where
"mem i \<equiv> IVar (Para (Ident ''mem'') i)"

type_synonym paraExpType="nat \<Rightarrow>expType"

 

abbreviation dataOut::"nat\<Rightarrow>expType" where
"dataOut DEPTH \<equiv> read (Ident ''mem'') DEPTH (IVar (Ident ''tail'' ))"


abbreviation rstForm::"formula" where
"rstForm  \<equiv>  (eqn rst HIGH)"

abbreviation emptyForm::"formula" where
"emptyForm  \<equiv>  (eqn emptyFifo HIGH)"
 
abbreviation pushForm::"formula" where
"pushForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push HIGH)) (eqn pop LOW)"

abbreviation popForm::"formula" where
"popForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push LOW)) (eqn pop HIGH)"

abbreviation nPushPopForm::"formula" where
"nPushPopForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push LOW)) (eqn pop LOW)"

abbreviation pushDataForm::"nat \<Rightarrow>formula" where
" pushDataForm D \<equiv>  (eqn dataIn (Const (index D)))"

abbreviation popDataForm::"nat\<Rightarrow>nat \<Rightarrow>formula" where
" popDataForm DEPTH D \<equiv>  (eqn (dataOut DEPTH) (Const (index D)))"

abbreviation nFullForm::"nat \<Rightarrow>formula" where
"nFullForm  DEPTH\<equiv>  neg (fullForm DEPTH)"

abbreviation nEmptyForm::"formula" where
"nEmptyForm \<equiv> neg emptyForm "



definition  vertexI::"node" where [simp]:
"vertexI \<equiv>Vertex  0"
definition  vertexL::"nat \<Rightarrow> node list" where [simp]:
"vertexL DEPTH  \<equiv>  vertexI # (map (%i. Vertex  i) ( upt 1  (2*(DEPTH + 1))))"

definition edgeL::"nat \<Rightarrow> edge list" where [simp]:
 "edgeL DEPTH \<equiv> [Edge vertexI ( Vertex 1)]								
		@(map (%i.  ( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) ) (upt 0  DEPTH ))  (* self-loop*)  
	  @(map (%i.  ( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) (upt 1  DEPTH ))  (* self-loop*)    
		@(map (%i.   ( Edge (Vertex (2 * i - 1))  (Vertex (2 * i + 1))) ) ( upt 1 DEPTH))	 
		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i - 1))) ) (  upt 1 DEPTH )) 
		@(map (%i.   ( Edge (Vertex (2 * i - 1))  (Vertex (2 * i + 2))) ) ( upt 1 DEPTH)) 
		@(map (%i.   ( Edge (Vertex(2 * i + 2))  (Vertex(2 * i))) ) (  upt 1 DEPTH))"


(*let ant aEdge =
	val (Edge (Vertex from) (Vertex to)) = aEdge
in
	(from = 0) => rst				//init
| 	((from%2) = 1) =>				
		(from = to) => nPushPop		//selfloop
	|	((from+2) = to) => push		//push with unkown data
	|	(from = (to+2)) => pop		//pop with unkown data
	|	pushData vOfDataIn		//push with data
|	pop						//pop with data
;*)
primrec node2Nat::"node \<Rightarrow> nat" where
"node2Nat (Vertex n) = n"


definition antOfRbFifo::"nat\<Rightarrow>edge\<Rightarrow>formula" where
"antOfRbFifo  D  edge\<equiv>
  (let from=node2Nat (source edge) in
   let to=node2Nat (sink edge) in
  ( if (	from = 0) then rstForm	else
     if (from=to) then nPushPopForm else
   ( if ((from mod 2) =1) then
     (
       if ((from + 2)=to) then pushForm else
       if (from=(to + 2)) then popForm else
       pushDataForm D )   else
     popForm)))"


(*let cons aEdge = 
	val (Edge (Vertex from) (Vertex to)) = aEdge
in
	((from%2) = 1) AND ((to%2) = 1) => 				
		(from = 1) => TAndList [empty,nFull]		//FIFO is empty
	|	(from = (2*DEPTH+1)) => TAndList [nEmpty,full]	//FIFO is full
	|	TAndList [nEmpty,nFull]					//FIFO of other size
|	(to = 2) => popData vOfDataIn					//read the write data
| 	TAndList []
;*)

definition consOfRbFifo::"nat\<Rightarrow>nat\<Rightarrow>edge \<Rightarrow>formula" where
"consOfRbFifo   D DEPTH edge \<equiv>
(let from=node2Nat (source edge) in
   let to=node2Nat (sink edge) in
(if 	(((from mod 2) = 1) \<and> ((to mod 2) = 1)) then
  (if (from = 1) then (andForm  emptyForm (nFullForm DEPTH)) else
   if (from = (2*DEPTH+1)) then (andForm nEmptyForm (fullForm DEPTH)) else
     andForm nEmptyForm (nFullForm DEPTH)
  )
else 
 (if (to = 2) then popDataForm DEPTH D
  else chaos)))"

definition rbFifoGsteSpec::"nat \<Rightarrow> nat\<Rightarrow>gsteSpec" where [simp]:
"rbFifoGsteSpec depth data\<equiv>Graph  vertexI (edgeL depth) (antOfRbFifo data)  (consOfRbFifo data depth)"

primrec applyPlusN::"expType\<Rightarrow>nat \<Rightarrow>nat \<Rightarrow>expType" where
"applyPlusN e bound  0=e" |
"applyPlusN e bound (Suc N) = uif ''+'' [applyPlusN  e bound N,   Const (index 1), Const (index bound)]"

definition tagFunOfRbfifio:: "nat \<Rightarrow> nat\<Rightarrow>nodeTagFuncList" where [simp]:
" tagFunOfRbfifio depth DATA  n \<equiv> 
  (let x=node2Nat n in
   let DataE=(Const (index DATA)) in
  (if (x = 0) then [] else
  (if ((x mod 2) = 1) then [eqn tail (applyPlusN head depth (x div 2 ))] else 
   (if (x = (2)) then [] else
   [eqn tail (applyPlusN head depth ((x div 2) - 1)), eqn ( read (Ident ''mem'') depth tail) DataE ]) ))
 )"

abbreviation branch1::"generalizeStatement" where 
"branch1 \<equiv> 
  (let S1=assign (Ident ''tail'',LOW) in
   let S2=assign (Ident ''head'',LOW) in
   let S3=assign (Ident ''full'',LOW) in
   let S4=assign (Ident ''empty'',HIGH) in
   Parallel [S1,S2,S3,S4])"

abbreviation branch2::"nat \<Rightarrow> nat\<Rightarrow>generalizeStatement" where 
"branch2 bound msba\<equiv> 
  (let S1=writeArr (Ident ''mem'')  bound tail dataIn in
   let tailPlus=uif ''+'' [tail,  (Const (index 1)),(Const (index bound))] in
   let S2=assign (Ident ''tail'',tailPlus) in
   let S3=assign (Ident ''full'', iteForm (eqn head tail) HIGH full) in
   let S4=assign (Ident ''empty'',LOW) in
   Parallel ([S2,S3,S4]@S1))"

abbreviation branch3::"nat\<Rightarrow>generalizeStatement" where 
"branch3 bound\<equiv> 
  (let S1=assign (Ident ''tail'',LOW) in
   let headPlus=uif ''+'' [head,  (Const (index 1)), (Const (index bound))] in
   let S2=assign (Ident ''head'',headPlus) in
   let S3=assign (Ident ''full'',LOW) in
   let S4=assign (Ident ''empty'',HIGH) in
   Parallel [S1,S2,S3,S4])" 

abbreviation rbfifo::"nat \<Rightarrow> nat\<Rightarrow>circuit1" where
"rbfifo msba d\<equiv>
  let regs=[Ident ''mem'', Ident ''tail'', Ident ''head'', Ident ''empty'', Ident ''full''] in
  let inputs=[Ident '' rst'', Ident ''dataIn'', Ident ''push'', Ident ''pop''] in
  let trans=caseStatement 
     [(eqn rst HIGH, branch1),
      (andForm (eqn push HIGH) (eqn full LOW), branch2 d msba),
      (andForm (eqn pop HIGH) (eqn emptyFifo LOW), branch3 d)] in
   Circuit1 inputs regs trans"

lemma substNIl: 
  shows "(substExp e [] = e) \<and> (substForm f [] =f)" sorry
  (*proof(induct_tac e and f, auto)
  by*)

lemma preCondIfNeg[simp]: 
  assumes a1:"(tautlogy (implyForm asm (neg b)) I)"
  shows " (tautlogy (implyForm asm (preCond1 f (If b S1 S2))) I)= 
  (tautlogy (implyForm asm (preCond1 f S2)) I)"
  proof(cut_tac a1,auto)qed

lemma preCondIfYes[simp]: 
  assumes a1:"(tautlogy (implyForm asm ( b)) I)"
  shows " (tautlogy (implyForm asm (preCond1 f (If b S1 S2))) I)= 
  (tautlogy (implyForm asm (preCond1 f S1)) I)"
  proof(cut_tac a1,auto)qed

lemma preCondCaseNeg[simp]: 
  
  assumes a1:"(tautlogy (implyForm asm (neg  b1)) I)"
  shows " (tautlogy
        (implyForm asm (preCond1 f (caseStatement ((b1,S1)#branchs)))) I)= (tautlogy
        (implyForm asm (preCond1 f (caseStatement (branchs)))) I)"
  proof(cut_tac a1,auto)qed   

lemma preCondCaseYes[simp]: 
  
  assumes a1:"(tautlogy (implyForm asm (  b1)) I)"
  shows " (tautlogy
        (implyForm asm (preCond1 f (caseStatement ((b1,S1)#branchs)))) I)= (tautlogy
        (implyForm asm (preCond1 f S1)) I)"
  proof(cut_tac a1,auto)qed     


lemma consistencyOfRbfifo:
  shows "consistent' (rbfifo msba depth) I (rbFifoGsteSpec depth data) (tagFunOfRbfifio depth data)"
  proof(unfold consistent'_def,rule allI,rule impI)
    fix e
    let ?G=" (rbFifoGsteSpec depth data)"
    let ?M="(rbfifo msba depth)"
    let ?tag="(tagFunOfRbfifio depth data)"
    let ?P ="\<lambda>e.  (let f = andListForm (tagFunOfRbfifio depth data (sink e)) in
             let f' = andListForm (tagFunOfRbfifio depth data (source e)) in 
             tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1 f  (nextFun1 ?M))) I )"
    let ?R="\<lambda>e f f'. tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1 f  (nextFun1 ?M))) I "
    let ?Q ="\<lambda> e f f' s. formEval I (implyForm (andForm f' (antOf ?G e)) (preCond1 f  (nextFun1 ?M))) s "
    let ?f = "andListForm (tagFunOfRbfifio depth data (sink e))"
    let ?f' ="andListForm (tagFunOfRbfifio depth data (source e))"
    assume a1:"e \<in> edgesOf (rbFifoGsteSpec depth data)"
    
    have "e=Edge vertexI ( Vertex 1) | 
           (\<exists>i. 0\<le>i \<and> i\<le> (depth) \<and>  e=( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) )   |
            (\<exists>i. 1\<le>i \<and> i\<le> (depth) \<and>  e=( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> depth \<and> e=( Edge (Vertex (2 * i - 1))  (Vertex (2 * i + 1))) ) |

           (\<exists>i. 1\<le>i \<and> i\<le> depth \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i - 1))) )  |
           (\<exists>i. 1\<le>i \<and> i\<le> depth \<and>  e= ( Edge (Vertex (2 * i - 1))  (Vertex (2 * i + 2))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> depth  \<and> e=( Edge (Vertex(2 * i + 2))  (Vertex(2 * i))))  "
      apply(cut_tac a1,auto)    done
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac b1, simp add:antOfRbFifo_def) done
     }
    moreover
    {assume b1:" (\<exists>i. 0\<le>i \<and> i\<le> depth \<and>  e=( Edge (Vertex (2* i + 1))  (Vertex (  2*i + 1))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }
    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> depth \<and>  e=( Edge (Vertex (2* i + 2))  (Vertex (  2*i + 2))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }
     moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> depth \<and> e=( Edge (Vertex (2 * i - 1))  (Vertex (2 * i + 1))) )   " (is "\<exists>i. ?asm i")
     from b1 obtain i where b1:"?asm i" by auto
     have b2:"(tautlogy (implyForm (andForm ?f' (antOf ?G e)) (neg (rstForm))) I)" sorry
     have b3:"(tautlogy (implyForm (andForm ?f' (antOf ?G e)) ( andForm (eqn push HIGH) (eqn full LOW))) I)" sorry
     have b5:"1 \<le> 2* i - 1 " apply(cut_tac b1,auto) done
     have b5a:"\<not>2 * i \<le> Suc 0" apply(cut_tac b1,auto) done
     have b5b:"(2 * i - Suc 0) mod 2 \<noteq> 0" apply(cut_tac b1,auto,arith) done
     have b5c:"(2 * i - Suc 0) div 2= (i - 1)" apply(linarith) done
     have b5d:"(2 * i - Suc 0) mod 2 = 1" apply(cut_tac b1,auto,arith) done
     have b5e:" 2 * i - Suc 0 \<noteq> Suc (2 * i)"  apply(cut_tac b1,auto) done

     have b6:" tautlogy (implyForm (andForm ?f' (antOf ?G e)) (preCond1 ?f  (nextFun1 ?M))) I "
     
     proof(cut_tac b2 b3,simp del:tautlogy_def preCondSimp2, cut_tac b1 b5 b5a b5b b5c, simp,rule allI,rule impI )
      fix s
      let ?e="Edge (Vertex (2 * i - Suc 0)) (Vertex (Suc (2 * i)))"
      assume c1:"s (Ident ''tail'') = expEval I (applyPlusN head depth (i - Suc 0)) s \<and>
         formEval I (antOfRbFifo data ?e) s "
      have c2:" s (Ident ''push'') = index 1"
          apply(cut_tac b1 c1 b5d b5e, unfold antOfRbFifo_def,auto) done
      show "I ''+'' [expEval I (applyPlusN head depth (i - Suc 0)) s, s (Ident ''push''), index depth] =
         expEval I
          (substExp (applyPlusN head depth i)
            ((Ident ''tail'', uif ''+'' [tail, Const (s (Ident ''push'')), Const (index depth)]) #
             (Ident ''full'', iteForm (eqn head tail) (Const (s (Ident ''push''))) full) #
             (Ident ''empty'', Const (s (Ident ''full''))) # map statement2Assigns (writeArr (Ident ''mem'') depth tail dataIn)))
          s "
      proof
      (*have "?P e"
      proof( simp add:Let_def )
  lemma noEffectSubstExp [intro!]:
  
  shows " (  (varOfExp e \<inter>  (varOfSent S) ={}) \<Longrightarrow>(substExp e S)  =e) "
by (metis noEffectSubstAux)
  
lemma noEffectSubstForm [intro!]:
  
  shows " 
             (varOfForm f \<inter>  (varOfSent S) ={}) \<Longrightarrow> (substFormByStatement f S)  =  f "
 by (metis noEffectSubstAux)     
      have "(tautlogy (implyForm asm (neg b)) I)"*)
      have "?Q e ?f ?f' s"
      proof(cut_tac b2, simp only:Let_def antOfRbFifo_def)
       apply(cut_tac b2, simp) done
    }


lemma varsOnCat[simp]:
  shows "varOfGenStatement (cat (Parallel S1) (Parallel S2))=(varOfGenStatement (Parallel S1) ) \<union> (varOfGenStatement (Parallel S2) )"
  apply(induct_tac S1)
  apply simp
by auto
  

lemma   forallVars:
  assumes a1:"\<forall> i.( varOfSent (paraForm i))\<inter> varSet ={}"
   shows  "(varOfSent (forallSent (down N) paraForm))\<inter> varSet ={}"
  proof(induct_tac N)
    show " varOfSent (forallSent (down 0) paraForm) \<inter> varSet = {}"
      apply(cut_tac a1,force) 
      done
  next
    fix n
    assume b1:"varOfSent (forallSent (down n) paraForm) \<inter> varSet = {}"
    have " (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \<union>
      (varOfSent (forallSent (down  n ) paraForm) )"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show "  varOfSent (forallSent (down (Suc n)) paraForm) \<inter> varSet = {}"
      apply(-,cut_tac a1,simp )
      by (metis (lifting) Int_Un_distrib2 Un_empty_left b1) 
  qed

lemma   forallVars1[simp,intro!]:
  assumes a1:"\<forall>i. v \<notin>( varOfSent (paraForm i))"
   shows  "v \<notin>(varOfSent (forallSent (down N) paraForm))" (is "?P N")
  proof(induct_tac N)
    show "?P 0"
      apply(cut_tac a1,force) 
      done
  next
    fix n
    assume b1:"?P n"
    have " (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \<union>
      (varOfSent (forallSent (down  n ) paraForm) )"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show "?P (Suc n) "
      apply(-,cut_tac a1,simp )
      by (metis (lifting) b1)
  qed
      
lemma varsOfForallSentIn[simp]:
  "i \<le>N \<longrightarrow>v \<in> varOfSent (paraForm i) \<longrightarrow> v \<in> varOfSent (forallSent (down N) paraForm)" ( is "?P N")
proof(induct_tac N)
  show "?P 0"
   by auto
   next
    fix N
   assume a1:"?P N" 
   show "?P (Suc N)"
   proof(rule impI)+
    
    assume b0:"i \<le> Suc N" and b1:"  v \<in> varOfSent (paraForm i)"  
    have b2:"  varOfSent  (forallSent (down (Suc N)) paraForm) = varOfSent (paraForm (Suc N)) \<union>   varOfSent (forallSent (down N) paraForm)"
     by (metis down.simps(2) downNIsNotEmpty paraTheory.moreSent varsOnCat) 
     have "i \<le> N | i=Suc N" by(cut_tac b0,auto)
    moreover
    {assume c1:"i \<le> N"
     have c2:" v \<in>varOfSent (forallSent (down N) paraForm)" 
     apply(cut_tac c1 b1 a1,auto) done
     then have "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by(cut_tac c1 c2 b2,auto)
     }
     moreover
    {assume c1:"i =Suc N"
     from c1  have "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by(cut_tac c1 b1 b2,auto) 
     }
    ultimately show "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by blast
  qed
 qed
     
lemma varsOfNot [simp,dest!]:
"v \<notin> set (map fst   (statement2Assigns S)) \<Longrightarrow>
 v \<in>set( map fst (statement2Assigns  (cat S S'))) = (v \<in> set (map fst   (statement2Assigns S'))) "
by (metis Un_iff varsOfSent1 varsOnCat)



lemma ForallSentForm [simp]:
  shows a1:" (statement2Assigns (forallSent (down N)  (\<lambda>i. assign (Para n i, e' i))))=map (\<lambda>i. (Para n i, e' i)) (down N)" (is "?P N")
proof(induct_tac N)
  show "?P 0"
    apply simp
    done
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N )"
  proof(cut_tac b1, simp)
    have b2:"\<exists> j xs. down N= j#xs"
      by (metis downNIsNotEmpty) 
  then obtain j xs where b2:"down N=j#xs" by blast
    show"  statement2Assigns (forallSent (Suc N # down N) (\<lambda>i. assign (Para n i, e' i))) = 
           (Para n (Suc N), e' (Suc N)) # map (\<lambda>i. (Para n i, e' i)) (down N)"
      apply(cut_tac b1 b2,simp)
      done
  qed
qed

subsection{*more lemmas on valOf operator*}

text{*more lemmas on valOf operator*}


lemma valOfLemma2Aux[simp]: "(var' \<notin> set (map fst xs)) \<longrightarrow> (valOf xs (var'))=IVar var'"
  apply(induct_tac xs)
  apply simp
  apply auto
done  

lemma valOfLemma2[simp,intro]: "(var' \<notin> set (map fst xs)) \<Longrightarrow> (valOf xs (var'))=IVar var'"
by (metis (lifting) valOfLemma2Aux)
  
lemma valOfLemma3 [simp]:"(\<forall> i.  var' \<noteq> Para v i) \<Longrightarrow>  (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) var')=IVar var'"
apply(rule valOfLemma2)
apply(induction N)
by auto

lemma valOfLemma4Aux :"v \<notin> set (map fst   (statement2Assigns S)) \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma4 [simp,intro]:"v \<notin> set (map fst   (statement2Assigns S)) \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
by (metis valOfLemma4Aux)

lemma valOfLemma5Aux :"( valOf (statement2Assigns   S ) v=IVar v) \<and>  
  ( valOf (statement2Assigns S') v=IVar v)\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) "
    proof(induct_tac S,auto)qed
    
lemma valOfLemma5 [simp,intro]:"( valOf (statement2Assigns   S ) v=IVar v) \<and>  
  ( valOf (statement2Assigns S') v=IVar v)  \<Longrightarrow> ( valOf (statement2Assigns  (cat S S')) v=IVar v) "
  by(metis  valOfLemma5Aux)
  
lemma valOfLemma6Aux :"( valOf (statement2Assigns   S ) v=IVar v) \<and>   
  ( valOf (statement2Assigns S') v=IVar v)\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) "
    proof(induct_tac S,auto)qed


lemma valOfLemma7Aux:"v \<notin> varOfSent S \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
proof(induct_tac S,auto)qed

lemma valOfLemma7 [simp,intro]:"v \<notin> varOfSent S \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
by(metis valOfLemma7Aux)

lemma valOfLemma8Aux:"v \<in> varOfSent S \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v"
proof(induct_tac S,auto)qed

lemma valOfLemma8A[simp,intro]:"v \<in> varOfSent S \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v"
by(metis valOfLemma8Aux)    


lemma noEffectValOfStatementAux[intro]:
  shows "( v \<notin>  (varOfSent S) )\<longrightarrow> valOf (statement2Assigns  S)  v=IVar v" (is "?P N") 
 proof(induct_tac S,auto)qed
 
  lemma noEffectValOfStatement[simp,intro]:
  assumes "( v \<notin>  (varOfSent S)) "
  shows   "valOf (statement2Assigns  S)  v=IVar v" (is "?P N")
by (metis assms valOfLemma2Aux varsOfSent1) 
 
 lemma noEffectValOfForallStatementAux[intro]:
  shows "( \<forall>i. (v\<notin>  (varOfSent (ps i)) ))\<longrightarrow> valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v" (is "?P N")
  proof(induct_tac N)
    show "?P 0"
      apply simp
      done
   next
    fix N
    assume b1:"?P N"
    show "?P (Suc N)"
    proof(rule impI)
      assume c1:" \<forall>i. v \<notin> varOfSent (ps i)"
      show "valOf (statement2Assigns (forallSent (down (Suc N)) ps)) v = IVar v"
      proof(rule noEffectValOfStatement)
        have "   varOfSent (forallSent (down (Suc N)) ps) \<inter>{v} = {}"  thm forallVars
        proof(rule  forallVars,cut_tac c1,auto)qed
        then show   " v \<notin> varOfSent (forallSent (down (Suc N)) ps)"
        by (metis c1 forallVars1) 
      qed
  qed 
  qed

text{*definitions and lemmas on  andList formula constructor*}   


primrec andList::"formula list \<Rightarrow> formula" where
"andList [] = chaos" |
"andList (frm#frms) = andForm frm (andList frms)" 
   
lemma andListFormAux1:
 
  shows "set fs \<subseteq>  fs' \<longrightarrow>( \<forall> inv. inv \<in> fs' \<longrightarrow>formEval inv s)\<longrightarrow> formEval (andList fs) s"
  proof(induct_tac fs,auto)qed
  
lemma andListForm1[simp,intro]:
 
  "\<lbrakk>set fs \<subseteq>  invs ; ( \<forall> inv. inv \<in>invs \<longrightarrow>formEval inv s)\<rbrakk>\<Longrightarrow> formEval (andList fs) s"
 by(metis  andListFormAux1)  


lemma andList2Aux:
   shows "formEval (neg frm) s \<longrightarrow> frm \<in>set frms \<longrightarrow> formEval (neg (andList frms)) s"
   proof(induct_tac frms,auto) qed
   
lemma andList2:
   shows "formEval (neg frm) s \<Longrightarrow> frm \<in>set frms \<Longrightarrow> formEval (neg (andList frms)) s"
   by (metis andList2Aux)
   
lemma andList1Aux:
   shows "formEval ( (andList frms)) s  \<longrightarrow> frm \<in>set frms \<longrightarrow> formEval ( frm) s "
   proof(induct_tac frms,auto)qed
   
lemma andList1:
   shows "formEval ( (andList frms)) s  \<Longrightarrow>  frm \<in>set frms \<Longrightarrow> formEval ( frm) s " 
    by (metis andList1Aux)
lemma resAux1:
  assumes   b:"formEval frm s" and c:"formEval (neg (andList (frm#frms))) s"
  shows"formEval (neg (andList frms)) s"
  apply(cut_tac b c)
  apply auto
  done


text{*If $asgns$ does not assign any variable in $E$ to any value, then evaluation of $E$ at the state $s$ is the same as that of $E$ 
at the state $transAux~ asgns~ s$ *}
lemma noEffectOnExpAux: 
  shows "(\<forall> s. (varOfExp E) \<inter>  set (map fst asgns) ={} \<longrightarrow>
  expEval E  s  =  expEval E (transAux asgns s))  \<and>
  (\<forall>   s. (varOfForm f) \<inter>  set (map fst asgns) ={} \<longrightarrow>
  formEval f s  =  formEval f (transAux asgns s))"
  (is "(\<forall>  s. ?P asgns s E) \<and>( \<forall>  s. ?Q asgns s f)")
proof(induct_tac E and f)

  fix varType
  let ?E="IVar varType"
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")
  proof(rule allI)
  fix s
  show "?R s asgns"
  proof( induct_tac asgns)
    show "?R s []" by simp
    next  
    fix a asgns  
    assume  a1:"?R s asgns"
    show "?R s (a#asgns)"    
    proof 

    assume c1:" varOfExp (?E) \<inter> set (map fst (a # asgns)) = {}"

      have d1:"\<exists> v val0. a=(v,val0)"
            by auto 
    then obtain var val0 where d2:"a=(var,val0)"
            by blast
     
     have f1:"expEval ?E s = expEval ?E (transAux ( asgns) s)"
          apply(cut_tac a1  c1 )
          apply auto
          done
      have f2:" expEval ?E (transAux (a # asgns) s)= expEval ?E (transAux ( asgns) s)"
          apply(cut_tac a1 c1,simp)
          apply( auto)
         done
      show " expEval ?E s = expEval ?E (transAux (a # asgns) s)"
         apply(cut_tac f1 f2, simp)
         done
     qed
   qed
  qed
next
  fix n
  
  let ?E="Const n"
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")  
  by auto
next
  fix frm e1 e2 
   let ?E="iteForm frm e1 e2"
  assume a1:"( \<forall>  s. ?Q asgns s frm)" and a2:"(\<forall>  s. ?P asgns s e1)" and a3:"(\<forall>  s. ?P asgns s e2)"
  
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")  
  proof(rule allI,rule impI)
  fix s
   assume c1:" varOfExp (?E) \<inter> set (map fst ( asgns)) = {}"
   show "expEval (iteForm frm e1 e2) s = expEval (iteForm frm e1 e2) (transAux asgns s)"
   apply(cut_tac a1 a2 a3 c1)
   apply auto
   done
   qed  
next
  fix e1 e2
  let ?f="eqn e1 e2" 
  assume a1:"(\<forall>  s. ?P asgns s e1)" and a2:"(\<forall>  s. ?P asgns s e2)"
  
  show "(\<forall>  s. ?Q asgns s ?f)" (is "\<forall>s. ?R s asgns")  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 f2
  let ?f="andForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 
  let ?f="neg f1 "
  assume a1:"( \<forall>  s. ?Q asgns s f1)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 ,auto) 
  qed
next
  fix f1 f2
  let ?f="orForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
fix f1 f2
  let ?f="implyForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
  show "( \<forall>  s. ?Q asgns s chaos)"
  by auto
qed
 

lemma noEffect: 
shows "(\<forall>   s. (varOfExp E) \<inter>  (varOfSent S) ={} \<longrightarrow> expEval E s  =  expEval E (trans S s)) \<and> 
(\<forall>s. varOfForm f \<inter>  (varOfSent S) ={}\<longrightarrow>
         formEval f s = formEval f (trans S s))"
apply(cut_tac  f="f" and E="E" and asgns="  ((statement2Assigns S))" in noEffectOnExpAux) 
apply(unfold trans_def)
apply(cut_tac S="S" in varsOfSent1)
apply metis
done

lemma noEffectOnExp: 
  assumes a1:"(varOfExp E) \<inter>  (varOfSent S) ={} "
    shows " expEval E s  =  expEval E (trans S s)"
by (metis assms noEffect) 


lemma noEffectOnFormula: 
  assumes a1:"(varOfForm f) \<inter>  (varOfSent S) ={} "
    shows " formEval f s  =  formEval f (trans S s)"
by (metis assms noEffect) 


   
text{*if varianles occurring in an expression e (or a formula f) is disjoint with that in a statement S, then 
substExpByStatement e S (or substFormByStatement f S)
is the same as e(or f)*} 
  
lemma noEffectSubstAux:
  
  shows " (  (varOfExp e \<inter>  (varOfSent S) ={}) \<longrightarrow>(substExpByStatement e S)  =e) \<and>
           (  (varOfForm f \<inter>  (varOfSent S) ={} )\<longrightarrow> (substFormByStatement f S)  =  f )"
           
    (is "(( ?condOne e S\<longrightarrow> ?LHS e S=?RHS e S)\<and> (?condOnf f S\<longrightarrow> ?LHS1 f S=?RHS1 f S))")
  proof(induct_tac e and f)
      fix v
      let ?e="(IVar v)"
      show  "?condOne ?e S\<longrightarrow>?LHS ?e S=?RHS ?e S"
      proof(induct_tac S)
        fix prod
        let ?S="assign prod"
        show "?condOne ?e ?S \<longrightarrow>?LHS ?e ?S=?RHS ?e ?S"
        
        apply(unfold  substExpByStatement_def trans_def,auto)
        done
    next
       fix prod S
       let ?S="parallel prod S"
       assume b1:"?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
       
       show "?condOne ?e ?S \<longrightarrow> ?LHS ?e ?S=?RHS ?e ?S"
       
       proof(unfold  substExpByStatement_def trans_def,
       case_tac "fst prod =v",force)
       assume d1:"fst prod \<noteq> v "
       show "varOfExp (IVar v) \<inter> varOfSent (parallel prod S) = {} \<longrightarrow> (substExp (IVar v) (statement2Assigns (parallel prod S))) =
               (IVar v)"
       proof(cut_tac d1,simp) qed
      
      qed 
    qed 
next 
  fix n
  let ?e="(Const n)"
      show  "?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
      apply( simp)
      done
next
  fix f e1 e2
  assume a1:" (?condOnf f S \<longrightarrow> ?LHS1 f S=?RHS1 f S)" and
  a2:"?condOne e1 S \<longrightarrow>?LHS e1 S=?RHS e1 S" and a3:"?condOne e2 S \<longrightarrow>?LHS e2 S=?RHS e2 S"
  let ?e="iteForm f e1 e2"
  show "?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"  
  proof(rule impI)
  assume b1:"?condOne ?e S"
  have c1:"?condOnf f S "
  apply(cut_tac b1,simp)
  by (metis bot_eq_sup_iff inf_sup_distrib2)
  have c2:"?condOne e1 S "
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
  have c3:"?condOne e2 S "
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
 with c1 c2 c3 a1 a2 a3
 show "?LHS ?e S=?RHS ?e S"
 by (metis substExpByStatement_def substExpite substFormByStatement_def)  
 qed 
 
next
  fix e1 e2
  
  assume a1:"?condOne e1 S \<longrightarrow>?LHS e1 S=?RHS e1 S" and a2:"?condOne e2 S \<longrightarrow>?LHS e2 S=?RHS e2 S"
  let ?f="eqn e1 e2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOne e1 S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 sup_eq_bot_iff)
  have c2:"?condOne e2 S"
  apply(cut_tac b1,simp)
   by (metis Int_Un_distrib2 sup_eq_bot_iff)
   with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
    by simp
   qed
next
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="andForm f1 f2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   qed
next
  fix f1
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)"
  let ?f="neg f1"
  show "( ?condOnf ?f S \<longrightarrow>?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  by(cut_tac b1,simp)
  
   with a1 c1
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   qed
 
next   
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="implyForm f1 f2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   
  qed
  
next
  let ?f="chaos"
  show "( ?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  by auto
next
  next   
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="orForm f1 f2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   
  qed
qed

lemma noEffectSubstExp [intro!]:
  
  shows " (  (varOfExp e \<inter>  (varOfSent S) ={}) \<Longrightarrow>(substExpByStatement e S)  =e) "
by (metis noEffectSubstAux)
  
lemma noEffectSubstForm [intro!]:
  
  shows " 
             (varOfForm f \<inter>  (varOfSent S) ={}) \<Longrightarrow> (substFormByStatement f S)  =  f "
 by (metis noEffectSubstAux) 
 
 
lemma  noEffectOnRule[simp,intro]:
  assumes a1:"  (varOfForm f \<inter>  (varOfSent (act r)) ={})"
  shows " invHoldForRule s f r R "  (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
  have "?P2 s"
  using assms noEffectSubstForm by auto
  then show "?P1 s \<or> ?P2 s \<or> ?P3 s"
  by auto
qed 
  
lemma noEffectValOfForallStatement[simp,intro]:
  shows "( \<forall>i. (v \<notin>  (varOfSent (ps i))) ) \<Longrightarrow>  valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v" 
  by(metis noEffectValOfForallStatementAux)
  
 lemma noEffectValOfForallStatement1[simp,intro]:
  shows "( \<forall>i. (v \<notin>  (varOfSent (ps i))) ) \<Longrightarrow>  expEval ( valOf (statement2Assigns  (forallSent (down N) ps)) v) s=s  v"
by auto




   (* [Edge vertexI ( Vertex 1)]								
		@(map (%i.  (Edge (Vertex (2 * i + 1))  (Vertex (2 *  i + 1))) ) (upt (0)  DEPTH))     
		@(map (%i.   ( Edge (Vertex (2 * i - 1))  (Vertex (2 * i + 1))) ) ( upt 1 DEPTH))	 

		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i - 1))) ) (  upt 1 DEPTH )) 
		@(map (%i.   ( Edge (Vertex (2 * i - 1))  (Vertex (2 * i + 2))) ) ( upt 1 DEPTH)) 
		@(map (%i.   ( Edge (Vertex(2 * i + 2))  (Vertex(2 * i))) ) (  upt 1 DEPTH))*)

abbreviation nEmptyForm::"formula" where
"nEmptyForm \<equiv> neg emptyForm "
(*
parameter	    MSBD = 63;
    parameter	    LAST = 15;
    parameter	    MSBA = 3;
    input	    clock;
    input           rst;
    input [MSBD:0]  dataIn;
    input	    push;
    input	    pop;
    output [MSBD:0] dataOut;
    output	    full;
    output	    empty;

    reg [MSBD:0]    mem[0:LAST];
    reg [MSBA:0]    tail;
    reg [MSBA:0]    head;
    reg		    empty;
    reg		    full;
    integer	    i;


if (rst) begin tail = 0;
			head = 0;
			full = 0;
	              empty = 1;
                 end
	else if (push & ~full) begin
	    mem[tail] = dataIn;
	    tail = tail + 1;
	    if (head == tail) full = 1;
	    empty = 0;
	end // if (push & ~full)
	else if (pop & ~empty) begin
	    head = head + 1;
	    if (tail == head)empty = 1;
	    full = 0;

lemma writeThenRead:
  assumes a1:"  preExp1 adr' ( (writeArr' a bound adr ce)) =  adr"
  shows " expEval (read a bound adr') (genTrans (writeArr' a bound adr ce) s) = expEval ce s"
proof -
  have " preExp1 (read a bound adr')  ( (writeArr' a bound adr ce)) =ce" (is "?P bound")
  proof(induct_tac bound)
    show "?P 0"
    proof(simp)
    
lemma consistentLemma:
  shows a1:"\<forall>sq. (consistent' M G tag \<longrightarrow>istrajOfCircuit1 M sq \<longrightarrow> isPathOf' p G
  \<longrightarrow> sqSatAssert sq p (antOf G) \<longrightarrow>   sqSatAssert sq p (consOf G))" (is " ?P p")
  proof(induct_tac p)
  show "?P []" 
  apply(rule allI,(rule impI)+) 
  using sqSatAssert.elims(3) by blast

lemma  preCondOnExp:
  assumes   a2:"stable M s" and a3:"stable M s"
  
  shows "( ( expEval (substExpByStatement e M) s =expEval e (transOfCircuit M s)) \<and>
           ( formEval (substFormByStatement f M) s = formEval f (transOfCircuit M s)))"
           
    (is "((  ?LHS e M=?RHS e M)\<and> ( ?LHS1 f M=?RHS1 f M))")
  proof(induct_tac e and f)
      fix v
      let ?e="(IVar v)"
      show  "?LHS ?e M=?RHS ?e M"
      proof(simp)
      
      proof(induct_tac M)
        fix prod
        let ?S="assign prod"
        show "?LHS ?e ?S=?RHS ?e ?S"
        
        apply(unfold  substExpByStatement_def trans_def,auto)
        done
    next
       fix prod S
       let ?S="parallel prod S"
       assume b1:"?LHS ?e S=?RHS ?e S"
       
       show "?LHS ?e ?S=?RHS ?e ?S"
       
       proof(unfold  substExpByStatement_def trans_def,
       case_tac "fst prod =v",force)
       assume d1:"fst prod \<noteq> v "
       show "expEval (substExp (IVar v) (statement2Assigns (parallel prod S))) s =
              expEval (IVar v) (transAux (statement2Assigns (parallel prod S)) s)"
       proof(cut_tac d1,simp,case_tac "(varOfExp ?e) \<inter>  set (map fst (statement2Assigns S) )={}")
        assume e1:"(varOfExp ?e) \<inter>  set (map fst (statement2Assigns S) )={}"
        have f1:"v \<notin> fst ` set (statement2Assigns S)"
        apply(cut_tac e1,simp)
        done
        have f2:" expEval ?e s  =  expEval ?e (transAux (statement2Assigns S) s)"
          apply(cut_tac e1)
          by (metis (no_types) noEffectOnExpAux)

        show " expEval (valOf (statement2Assigns S) v) s = transAux (statement2Assigns S) s v"
        using b1 by auto
        
        next
        assume  e1:"(varOfExp ?e) \<inter>  set (map fst (statement2Assigns S) )\<noteq>{}"
        have f1:"v \<in> fst ` set (statement2Assigns S)"
        apply(cut_tac e1,simp)
        done
      show " expEval (valOf (statement2Assigns S) v) s = transAux (statement2Assigns S) s v"
        using b1 by auto 
      qed 
    qed
  qed
next 
  fix n
  let ?e="(Const n)"
      show  "?LHS ?e S=?RHS ?e S"
      apply( simp)
      done
next
  fix f e1 e2
  assume a1:" ( ?LHS1 f S=?RHS1 f S)" and
  a2:"?LHS e1 S=?RHS e1 S" and a3:"?LHS e2 S=?RHS e2 S"
  let ?e="iteForm f e1 e2"
  show "?LHS ?e S=?RHS ?e S"
  using a1 a2 a3 by auto
next
  fix e1 e2
  
  assume a1:"?LHS e1 S=?RHS e1 S" and a2:"?LHS e2 S=?RHS e2 S"
  let ?f="eqn e1 e2"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 a2 by auto 
next
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="andForm f1 f2"
  
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 a2 by auto  
next
  fix f1
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)"
  let ?f="neg f1"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 by auto
next   
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="implyForm f1 f2"
  
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  using a1 a2 by auto
next
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="orForm f1 f2"
  
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  using a1 a2 by auto
next
  let ?f="chaos"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  by auto
qed

definition tautlogy::"formula \<Rightarrow> bool" where [simp]:
"tautlogy f \<equiv> \<forall>s. formEval f s"

primrec andListForm::"formula list \<Rightarrow> formula " where
"andListForm [] = chaos" |
"andListForm  (f#fs) = andForm f (andListForm  fs)"
 
definition consistent'::"circuit \<Rightarrow> gsteSpec \<Rightarrow> nodeTagFuncList \<Rightarrow> bool" where [simp]:
"consistent' M G tag \<equiv>( \<forall>e. 
  (e \<in> edgesOf G \<longrightarrow> (
  let f=andListForm (tag (sink e)) in
  (tautlogy (preCond f (antOf G e) M)) \<or>
  (\<exists>f'. f' \<in>(set  (tag (source e))) \<and>
  tautlogy (implyForm f' (preCond f (antOf G e) M))))))"

lemma sqSatConsisitentGraph:
  assumes a1:"consistent' M G tag"
  shows "stable M s \<longrightarrow> transOfCircuit M s s' \<longrightarrow>e \<in> edgesOf G \<longrightarrow>
  formEval (andListForm (tag (source e))) s\<longrightarrow> formEval (antOf G e) s \<longrightarrow>
  formEval (andListForm (tag (sink e))) s'"
   

lemma consistentLemma:
  shows a1:"\<forall>sq. (consistent' M G tag \<longrightarrow>istrajOfCircuit M sq \<longrightarrow> isPathOf' p G
  \<longrightarrow> sqSatAssert sq p (antOf G) \<longrightarrow>   sqSatAssert sq p (consOf G))" (is " ?P p")
  proof(induct_tac p)
  show "?P []" apply (rule allI, case_tac "sq =[]", auto)
    by (meson list.distinct(1) sqSatAssert.elims(3))
  next
  fix e p
  assume b1:"?P p"
  show "?P (e#p)"
  proof(rule allI,(rule impI)+)
    have "sq=s#sq'" sorry
\<and>
  (\<forall>e s . (formEval (andListForm (tag (source e))) s) \<longrightarrow> formEval (antOf G e) s \<longrightarrow>   formEval (consOf G e) s)
    
  
  
  proof(unfold circuitSatGsteSpec_def,(rule allI)+,(rule impI)+)

text{*Here we must point out the fact that the assignments in a parallel assignment is executed in parallel, therefore we always assign an evaluation of an expression in the state $s$ to the corresponding variable.*}



text{*The reachable sate set of a protocol, which is describled by a set of initiate formulas and a set of rules, can be formalized inductively as follows:*}


inductive_set reachableSet::" formula set\<Rightarrow> rule set \<Rightarrow>state set" 
  for  inis::"formula set"  and rules::"rule set"   where

initState:  "\<lbrakk>formEval  ini s; ini \<in>  inis\<rbrakk>  \<Longrightarrow>(  s \<in>  ( reachableSet inis rules))" |

oneStep:    " \<lbrakk>s \<in>  reachableSet inis rules ;
               r \<in>   rules ;formEval (pre r ) s \<rbrakk> \<Longrightarrow>  trans  (act r ) s  \<in>  reachableSet inis rules"

text{*The rule $\mathsf{initState}$ says that a state $s$ is in $\mathsf{reachableSet}~inis~ rules$ if
 there exists a formula $ini$ that is true in state $s$. Next rule $\mathsf{oneStep}$ says that 
$$\mathsf{ trans}~  ($\mathsf{act}~ r )~ s $ is also in
 $\mathsf{reachableSet}~inis~ rules$ if $s$ already is in 
 $\mathsf{reachableSet}~inis~ rules$ and $r \<in> rules$.*}






text{*Functions $\mathsf{varIsOnVar}~x~x'$, $\mathsf{varIsOnExp}~x~e$,  $\mathsf{varIsOnForm}~x~f$, and  $\mathsf{varIsOnSent}~x~S$ 
define whether a pattern variable $x$  occurs in a target variable $x'$, expression $e$, a formula $f$, and a statement $S$. Namely, $x$ 
occurs in the above targets. 
For instance, for the statement   $S=\mathsf{assign}~  ((\mathsf{Para}~  ''n''~ i), (\mathsf{Const} ~1))$, variable  $x=\mathsf{Global}~''x''$ does not occur in it, hence $ \neg  $\mathsf{varIsOnSent}~x~S$.  *}

definition varIsOnVar::"varType \<Rightarrow> varType \<Rightarrow> bool"  where  [simp]:
" varIsOnVar pat  target = (pat =target)" 

primrec varIsOnExp::"varType \<Rightarrow> expType \<Rightarrow> bool"  where  
"varIsOnExp x (IVar v) = varIsOnVar x   v" |
"varIsOnExp x (Const j) =  False " 


primrec  varIsOnForm::"varType\<Rightarrow> formula \<Rightarrow> bool"  where 
"varIsOnForm x  (eqn e1 e2) = ( (varIsOnExp x  e1 ) \<or>  (varIsOnExp x e2))" |
"varIsOnForm x  ( andForm f1 f2) =(  (varIsOnForm x f1 ) \<or>  (varIsOnForm x f2 ))"|
"varIsOnForm x  (neg f1 ) = (  (varIsOnForm x  f1 ))"|
"varIsOnForm x  (orForm f1 f2) =(  (varIsOnForm x  f1 )  \<or>   (varIsOnForm x f2 ))"|
"varIsOnForm  x (implyForm f1 f2) = (  (varIsOnForm x f1 ) \<or>  (varIsOnForm x f2 ))"

primrec  varIsOnSent::"varType \<Rightarrow> statement \<Rightarrow> bool" where
" varIsOnSent x (assign a)=( varIsOnVar x (fst a)) "|
" varIsOnSent x ( parallel a sent2)= (( varIsOnVar x (fst a)) \<or>  (varIsOnSent x sent2))"

primrec assignsOf::"statement \<Rightarrow> assignType set" where
"assignsOf (assign a) ={a}" |
"assignsOf (parallel a S)= {a} \<union> assignsOf S"



definition varsOfVar::" varType \<Rightarrow> varType set"  where  [simp]:
" varsOfVar x  = {x}" 

primrec varOfExp::"expType \<Rightarrow> varType set"  and
  varOfForm::"formula \<Rightarrow> varType set"  where 
"varOfExp  (IVar v) =   varsOfVar v" |
"varOfExp   (Const j) =  {}" |

"varOfExp   (iteForm f e1 e2) =(varOfForm f) \<union>  (varOfExp   e1 )  \<union>   (varOfExp  e2)" |

"varOfForm   (eqn e1 e2) = ( (varOfExp   e1 )  \<union>   (varOfExp  e2))" |
"varOfForm   ( andForm f1 f2) =(  (varOfForm  f1 )  \<union>  (varOfForm  f2 ))"|
"varOfForm   (neg f1 ) = (  (varOfForm   f1 ))"|
"varOfForm   (orForm f1 f2) =(  (varOfForm   f1 )   \<union>   (varOfForm  f2 ))"|
"varOfForm   (implyForm f1 f2) = (  (varOfForm  f1 )  \<union>  (varOfForm f2 ))"|
"varOfForm   (chaos) ={}"

primrec  varOfSent::"statement \<Rightarrow> varType set" where
" varOfSent  (assign a)=( varsOfVar  (fst a)) "|
" varOfSent  ( parallel a sent2)= (( varsOfVar  (fst a)) \<union>  (varOfSent  sent2))"





lemma downNIsNotEmpty:
  "\<exists> j xs. down N= j#xs" (is "?P N")
  proof(induct_tac N,auto)
qed   



lemma noEffectOnExpAux: 
  shows "(\<forall>   s. (varOfExp E) \<inter>  set (map fst asgns) ={} \<longrightarrow>
  expEval E  s  =  expEval E (transAux asgns s))
  \<and>
  (\<forall>   s. (varOfForm f) \<inter>  set (map fst asgns) ={} \<longrightarrow>
  formEval f s  =  formEval f (transAux asgns s))"
  (is "(\<forall>  s. ?P asgns s E) \<and>( \<forall>  s. ?Q asgns s f)")
proof(induct_tac E and f)

  fix varType
  let ?E="IVar varType"
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")
  proof(rule allI)
  fix s
  show "?R s asgns"
  proof( induct_tac asgns)
    show "?R s []" by simp
    next  
    fix a asgns  
    assume  a1:"?R s asgns"
    show "?R s (a#asgns)"    
    proof 

    assume c1:" varOfExp (?E) \<inter> set (map fst (a # asgns)) = {}"

      have d1:"\<exists> v val0. a=(v,val0)"
            by auto 
    then obtain var val0 where d2:"a=(var,val0)"
            by blast
    (*have b1':"(\<forall> f s. ?P asgns s f)"
          by(cut_tac b1,simp)*)
     have f1:"expEval ?E s = expEval ?E (transAux ( asgns) s)"
          
          apply(cut_tac a1  c1 )
          apply auto
          done
      have f2:" expEval ?E (transAux (a # asgns) s)= expEval ?E (transAux ( asgns) s)"
          apply(cut_tac a1 c1,simp)
          apply( auto)
         done
      show " expEval ?E s = expEval ?E (transAux (a # asgns) s)"
         apply(cut_tac f1 f2, simp)
         done
     qed
   qed
  qed
next
  fix n
  
  let ?E="Const n"
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")  
  by auto
next
  fix frm e1 e2 
   let ?E="iteForm frm e1 e2"
  assume a1:"( \<forall>  s. ?Q asgns s frm)" and a2:"(\<forall>  s. ?P asgns s e1)" and a3:"(\<forall>  s. ?P asgns s e2)"
  
  show "(\<forall>  s. ?P asgns s ?E)" (is "\<forall>s. ?R s asgns")  
  proof(rule allI,rule impI)
  fix s
   assume c1:" varOfExp (?E) \<inter> set (map fst ( asgns)) = {}"
   show "expEval (iteForm frm e1 e2) s = expEval (iteForm frm e1 e2) (transAux asgns s)"
   apply(cut_tac a1 a2 a3 c1)
   apply auto
   done
   qed  
next
  fix e1 e2
  let ?f="eqn e1 e2"
  assume a1:"(\<forall>  s. ?P asgns s e1)" and a2:"(\<forall>  s. ?P asgns s e2)"
  
  show "(\<forall>  s. ?Q asgns s ?f)" (is "\<forall>s. ?R s asgns")  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 f2
  let ?f="andForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) 
  qed
next
  fix f1 
  let ?f="neg f1 "
  assume a1:"( \<forall>  s. ?Q asgns s f1)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 ,auto) 
  qed
next
  fix f1 f2
  let ?f="orForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
fix f1 f2
  let ?f="implyForm f1 f2"
  assume a1:"( \<forall>  s. ?Q asgns s f1)" and  a2:"( \<forall>  s. ?Q asgns s f2)"
  show "( \<forall>  s. ?Q asgns s ?f)"
  
  proof(rule allI,rule impI,cut_tac a1 a2,auto) qed
next
  show "( \<forall>  s. ?Q asgns s chaos)"
  by auto
qed


lemma varsOfSent1:
  " (varOfSent S) = set (map fst (statement2Assigns S))"
  proof(induct_tac S,auto) qed 
 

lemma noEffect: shows "(\<forall>   s. (varOfExp E) \<inter>  (varOfSent S) ={} \<longrightarrow> expEval E s  =  expEval E (trans S s)) \<and> 
(\<forall>s. varOfForm f \<inter>  (varOfSent S) ={}\<longrightarrow>
         formEval f s = formEval f (trans S s))"
apply(cut_tac  f="f" and E="E" and asgns="  ((statement2Assigns S))" in noEffectOnExpAux) 
apply(unfold trans_def)
apply(cut_tac S="S" in varsOfSent1)
apply metis
done

lemma noEffectOnExp: 
  assumes a1:"(varOfExp E) \<inter>  (varOfSent S) ={} "
    shows " expEval E s  =  expEval E (trans S s)"
by (metis assms noEffect) 


lemma noEffectOnFormula: 
  assumes a1:"(varOfForm f) \<inter>  (varOfSent S) ={} "
    shows " formEval f s  =  formEval f (trans S s)"
by (metis assms noEffect) 


primrec valOf::"assignType list \<Rightarrow> varType =>expType"  where
"valOf [] v=IVar v" |
"valOf (x#xs) v= (if ((fst x) =v) then (snd x) else valOf xs v)"

primrec substExp :: "expType\<Rightarrow> assignType list \<Rightarrow>expType"  and 
substForm ::"formula \<Rightarrow> assignType list \<Rightarrow> formula" where 
(*substExpVar: "substExp  (IVar v') asgns= (if ( \<not>wellformedAssgnList asgns ) then (IVar v')
                             else if (v' \<in> set (map fst asgns)) then  (valOf  asgns v') else (IVar v'))" |*)

substExpVar: "substExp  (IVar v') asgns=   (valOf  asgns v')  "| 

substExpConst: "substExp  (Const i)  asgns= Const i" |

substExpite: "substExp  (iteForm f e1 e2)  asgns= (iteForm (substForm f asgns) (substExp e1  asgns) (substExp e2  asgns))"| 
"substForm (eqn l r)  asgns=(eqn (substExp l  asgns) (substExp r  asgns))"  |
"substForm ( andForm f1 f2)  asgns =   ( andForm (substForm f1  asgns)  (substForm f2  asgns))"|
"substForm (neg f1 )   asgns= (neg ( substForm f1  asgns ))"|
"substForm (orForm f1 f2)   asgns= ( orForm (substForm f1  asgns )  (substForm f2  asgns))"|
"substForm (implyForm f1 f2)   asgns= (implyForm (substForm f1 asgns)  (substForm f2  asgns))" |
"substForm  chaos   asgns=chaos"

definition  substExpByStatement ::"expType \<Rightarrow>statement \<Rightarrow>expType"   where [simp]:
"substExpByStatement e S\<equiv>substExp e (statement2Assigns S)" 

definition substFormByStatement ::"formula \<Rightarrow>statement \<Rightarrow>formula"   where [simp]:
"substFormByStatement f S\<equiv>substForm f (statement2Assigns S)" 


definition statementEnableForm::"rule \<Rightarrow> formula\<Rightarrow>bool" where  [simp]:
" statementEnableForm  r f \<equiv>
  \<forall>s. formEval (pre r) s \<longrightarrow> formEval  (substFormByStatement f (act r)) s"

definition statementDisableForm::"rule  \<Rightarrow> formula \<Rightarrow> bool" where  [simp]:
" statementDisableForm r f \<equiv>
     \<forall>s. formEval (pre r) s \<longrightarrow> \<not> formEval  (substFormByStatement f (act r)) s "




lemma  preCondOnExp:
  
  shows "( ( expEval (substExpByStatement e S) s =expEval e (trans S s)) \<and>
           ( formEval (substFormByStatement f S) s = formEval f (trans S s)))"
           
    (is "((  ?LHS e S=?RHS e S)\<and> ( ?LHS1 f S=?RHS1 f S))")
  proof(induct_tac e and f)
      fix v
      let ?e="(IVar v)"
      show  "?LHS ?e S=?RHS ?e S"
      proof(induct_tac S)
        fix prod
        let ?S="assign prod"
        show "?LHS ?e ?S=?RHS ?e ?S"
        
        apply(unfold  substExpByStatement_def trans_def,auto)
        done
    next
       fix prod S
       let ?S="parallel prod S"
       assume b1:"?LHS ?e S=?RHS ?e S"
       
       show "?LHS ?e ?S=?RHS ?e ?S"
       
       proof(unfold  substExpByStatement_def trans_def,
       case_tac "fst prod =v",force)
       assume d1:"fst prod \<noteq> v "
       show "expEval (substExp (IVar v) (statement2Assigns (parallel prod S))) s =
              expEval (IVar v) (transAux (statement2Assigns (parallel prod S)) s)"
       proof(cut_tac d1,simp,case_tac "(varOfExp ?e) \<inter>  set (map fst (statement2Assigns S) )={}")
        assume e1:"(varOfExp ?e) \<inter>  set (map fst (statement2Assigns S) )={}"
        have f1:"v \<notin> fst ` set (statement2Assigns S)"
        apply(cut_tac e1,simp)
        done
        have f2:" expEval ?e s  =  expEval ?e (transAux (statement2Assigns S) s)"
          apply(cut_tac e1)
          by (metis (no_types) noEffectOnExpAux)

        show " expEval (valOf (statement2Assigns S) v) s = transAux (statement2Assigns S) s v"
        using b1 by auto
        
        next
        assume  e1:"(varOfExp ?e) \<inter>  set (map fst (statement2Assigns S) )\<noteq>{}"
        have f1:"v \<in> fst ` set (statement2Assigns S)"
        apply(cut_tac e1,simp)
        done
      show " expEval (valOf (statement2Assigns S) v) s = transAux (statement2Assigns S) s v"
        using b1 by auto 
      qed 
    qed
  qed
next 
  fix n
  let ?e="(Const n)"
      show  "?LHS ?e S=?RHS ?e S"
      apply( simp)
      done
next
  fix f e1 e2
  assume a1:" ( ?LHS1 f S=?RHS1 f S)" and
  a2:"?LHS e1 S=?RHS e1 S" and a3:"?LHS e2 S=?RHS e2 S"
  let ?e="iteForm f e1 e2"
  show "?LHS ?e S=?RHS ?e S"
  using a1 a2 a3 by auto
next
  fix e1 e2
  
  assume a1:"?LHS e1 S=?RHS e1 S" and a2:"?LHS e2 S=?RHS e2 S"
  let ?f="eqn e1 e2"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 a2 by auto 
next
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="andForm f1 f2"
  
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 a2 by auto  
next
  fix f1
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)"
  let ?f="neg f1"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
   using a1 by auto
next   
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="implyForm f1 f2"
  
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  using a1 a2 by auto
next
  fix f1 f2
  assume a1:" ( ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" ( ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="orForm f1 f2"
  
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  using a1 a2 by auto
next
  let ?f="chaos"
  show "( ?LHS1 ?f S=?RHS1 ?f S)"
  by auto
qed





definition invHoldForRule1'::" state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow> bool" where [simp]:
"invHoldForRule1' s f  r \<equiv>  
 (  formEval (pre r) s \<longrightarrow>  formEval  (substFormByStatement f  (act r)) s )"

 definition invHoldForRule2'::" state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow> bool" where [simp]:
"invHoldForRule2' s f  r \<equiv>  (  formEval  (substFormByStatement f  (act r)) s  =  formEval f s)"

definition  invHoldForRule3'::"state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow>formula set\<Rightarrow> bool"  where [simp]:
" invHoldForRule3' s f r fs  \<equiv>  
  (let pref=substFormByStatement f (act r) in
  ( \<exists>f'. f' \<in> fs \<and>  (formEval   (andForm (pre r)  f') s\<longrightarrow> formEval  pref s)))"
  
primrec andListForm::"formula list \<Rightarrow> formula " where
"andListForm [] = chaos" |
"andListForm  (f#fs) = andForm f (andListForm  fs)"

definition andSetForm::"formula set \<Rightarrow> formula " where
"andSetForm fs == Finite_Set.fold  andForm chaos  fs"
  



abbreviation invHoldForRule'::"state \<Rightarrow>formula \<Rightarrow> rule \<Rightarrow> (formula set) \<Rightarrow> bool" where
  "invHoldForRule' s inv0 r invs \<equiv>
    invHoldForRule1' s inv0 r \<or>  invHoldForRule2' s inv0 r \<or>
   invHoldForRule3' s inv0 r invs "



definition newconsistent::"formula set \<Rightarrow> formula set \<Rightarrow> rule set \<Rightarrow>bool"  where
"newconsistent invs inis rs \<equiv>
(\<forall>inv ini s. (inv \<in> invs \<longrightarrow> ini\<in> inis\<longrightarrow> formEval ini s \<longrightarrow> formEval inv s)) \<and>
 (\<forall> inv r s.  (inv \<in>invs  \<longrightarrow> r \<in> rs \<longrightarrow> invHoldForRule' s inv r invs  ))"   
 
 
 

lemma newconsistentLemma:
  assumes a1:"newconsistent invs inis rs" and a2:"s \<in> reachableSet inis rs" 
  shows "\<forall> inv. inv \<in> invs \<longrightarrow>formEval inv s"  (is "?P s")
  using a2
  proof induct
    case (initState ini s)
    show "?P s"
      apply(cut_tac a1, unfold newconsistent_def)
      by (metis (lifting) initState(1) initState(2))
  next
    case (oneStep s r)
    show "?P  (trans (act r) s)"    
    proof (rule allI, rule impI)
      fix inv
      assume b1:"inv \<in> invs"
      have b2:" invHoldForRule3' s inv r  invs \<or> invHoldForRule2' s inv r   \<or> invHoldForRule1' s inv r  "
        apply(cut_tac a1, unfold newconsistent_def)
        by (metis b1 oneStep(3))
        
     moreover
      {   assume c1:"invHoldForRule3' s inv r invs"
        
        let ?pref="substFormByStatement inv (act r)"
          have b3:"  ( (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval f'  s) \<longrightarrow>formEval (pre r)  s\<longrightarrow> formEval  ?pref s)  "  (is " ?P fs ")
           apply (cut_tac c1, unfold invHoldForRule3'_def,auto)
          done

        then have b3':"?P fs  "
          by blast

        have b4:" (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval f'  s)"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:"formEval (pre r) s"
          by (metis (lifting) oneStep(4))

        have b6:"formEval ?pref s"
         by(cut_tac b4 b5 b3', auto)

          have "formEval inv (trans (act r) s)"
            apply(cut_tac b6,metis preCondOnExp)
            done
      }
     
     moreover
      {assume b1':"invHoldForRule2' s inv r "
        have b2:"formEval inv s"
        by (metis b1 oneStep.hyps(2))
        
        let ?pref="substFormByStatement inv (act r)"
        have b3:" (  formEval  ?pref s  =  formEval inv s)"
        by(cut_tac b1',unfold  invHoldForRule2'_def,simp)
        
        with b2 have b4:"formEval ?pref s"
          by auto
          
        have "formEval inv (trans (act r) s)"
        by (cut_tac b4,  metis preCondOnExp)
          (*  apply(rule noEffect0)
          apply(cut_tac b1')
          apply (metis invHoldForRule2_def)
          by(metis b2)*)
      }
      moreover
      {assume b1':"invHoldForRule1' s inv r "
         
         have b5:"formEval (pre r) s"
          by (metis (lifting) oneStep(4))
        
         have "formEval inv (trans (act r) s)"
           apply(subgoal_tac "formEval (substFormByStatement inv (act r)) s")
           apply (metis preCondOnExp)
           apply(cut_tac b1' b5)
           by(unfold invHoldForRule1'_def,auto)
       
       }
       ultimately show "formEval inv (trans (act r) s)"
         by blast
     qed
   qed  
   
text{*lemma on forallForm formula constructor*}   
   
lemma andListFormAux1:
 
  shows "set fs \<subseteq>  fs' \<longrightarrow>( \<forall> inv. inv \<in> fs' \<longrightarrow>formEval inv s)\<longrightarrow> formEval (andListForm fs) s"
  proof(induct_tac fs,auto)qed
  
lemma andListForm1[simp,intro]:
 
  "\<lbrakk>set fs \<subseteq>  invs ; ( \<forall> inv. inv \<in>invs \<longrightarrow>formEval inv s)\<rbrakk>\<Longrightarrow> formEval (andListForm fs) s"
 by(metis  andListFormAux1)
 
 


lemma forall1:
  shows "\<forall> i. i \<le> N \<longrightarrow>formEval (forallForm (down N) pf ) s\<longrightarrow>formEval (pf i) s" (is "?P N")  
proof(induct_tac N)
    show "?P  0"
      by simp
  next
    fix N
    assume b1:"?P N"
    show "?P  (Suc N)"
      proof(case_tac "N =0")
        assume c1:"N=0"
        show "?P  (Suc N)"
        proof(cut_tac c1, auto,case_tac "i=0", auto,case_tac "i=1",auto)qed
      next
        assume c1:"N\<noteq>0"
        have "0<N " 
          by(cut_tac c1, arith)
       then have c2:"\<exists> N'. down (Suc N)=(Suc N)#N#down N'"
         by (metis down.simps(2) gr0_conv_Suc)
       then obtain N' where c2:"down (Suc N)=(Suc N)#N#down N'"
         by blast
       then have c3:"(N#down N')=down N"
         by simp
       show "?P  (Suc N)"      
       proof(rule allI,(rule impI)+,cut_tac c2,simp)
         fix i
         assume d1:"i\<le> Suc N" and d2:" formEval (pf (Suc N)) s \<and> formEval (forallForm (N # down N') pf) s"
         have "i=Suc N \<or> i<Suc N" 
           by (cut_tac d1, arith)
         moreover
         {assume e1:"i=Suc N"
           have " formEval (pf i) s"
             by (metis (lifting) d2 e1)
         }
         moreover
         {assume e1:"i<Suc N"           
           have " formEval (pf i) s"
             by (metis b1 c3 d1 d2 le_Suc_eq)
         }
         ultimately show "formEval (pf i) s"
           by blast
       qed
     qed
   qed

lemma forallLemma [simp,dest]:
  assumes a1:"i \<le> N" and a2:"formEval (forallForm (down N) pf ) s"
  shows "formEval (pf i) s"
by (metis a1 a2 forall1)      

section{*lemmas on varsOf*}  
definition varsOfVar::" varType \<Rightarrow> varType set"  where  [simp]:
" varsOfVar x  = {x}" 

primrec varOfExp::"expType \<Rightarrow> varType set"  and
  varOfForm::"formula \<Rightarrow> varType set"  where 
"varOfExp  (IVar v) =   varsOfVar v" |
"varOfExp   (Const j) =  {}" |
"varOfExp   top={}"|
"varOfExp   unKnown={}"|
"varOfExp   (iteForm f e1 e2) =(varOfForm f) \<union>  (varOfExp   e1 )  \<union>   (varOfExp  e2)" |

"varOfForm   (eqn e1 e2) = ( (varOfExp   e1 )  \<union>   (varOfExp  e2))" |
"varOfForm   ( andForm f1 f2) =(  (varOfForm  f1 )  \<union>  (varOfForm  f2 ))"|
"varOfForm   (neg f1 ) = (  (varOfForm   f1 ))"|
"varOfForm   (orForm f1 f2) =(  (varOfForm   f1 )   \<union>   (varOfForm  f2 ))"|
"varOfForm   (implyForm f1 f2) = (  (varOfForm  f1 )  \<union>  (varOfForm f2 ))"|
"varOfForm   (chaos) ={}"


lemma varsOnCat[simp]:
  shows "varOfSent (cat S1 S2)=(varOfSent S1 ) \<union> (varOfSent S2 )"
  apply(induct_tac S1)
apply (metis (lifting) cat1 varOfSent.simps(1) varOfSent.simps(2))
by (metis Un_assoc cat2 varOfSent.simps(2))
  

lemma   forallVars:
  assumes a1:"\<forall> i.( varOfSent (paraForm i))\<inter> varSet ={}"
   shows  "(varOfSent (forallSent (down N) paraForm))\<inter> varSet ={}"
  proof(induct_tac N)
    show " varOfSent (forallSent (down 0) paraForm) \<inter> varSet = {}"
      apply(cut_tac a1,force) 
      done
  next
    fix n
    assume b1:"varOfSent (forallSent (down n) paraForm) \<inter> varSet = {}"
    have " (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \<union>
      (varOfSent (forallSent (down  n ) paraForm) )"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show "  varOfSent (forallSent (down (Suc n)) paraForm) \<inter> varSet = {}"
      apply(-,cut_tac a1,simp )
      by (metis (lifting) Int_Un_distrib2 Un_emptsectiony_left b1) 
  qed

lemma   forallVars1[simp,intro!]:
  assumes a1:"\<forall>i. v \<notin>( varOfSent (paraForm i))"
   shows  "v \<notin>(varOfSent (forallSent (down N) paraForm))" (is "?P N")
  proof(induct_tac N)
    show "?P 0"
      apply(cut_tac a1,force) 
      done
  next
    fix n
    assume b1:"?P n"
    have " (varOfSent (forallSent (down (Suc n)) paraForm) )  =
      (varOfSent ( paraForm (Suc n)) ) \<union>
      (varOfSent (forallSent (down  n ) paraForm) )"
      by (metis (hide_lams, no_types) add_0_right moreSent down.simps(1) down.simps(2) nat.exhaust varsOnCat)
      then show "?P (Suc n) "
      apply(-,cut_tac a1,simp )
      by (metis (lifting) b1)
  qed
      
lemma varsOfForallSentIn[simp]:
  "i \<le>N \<longrightarrow>v \<in> varOfSent (paraForm i) \<longrightarrow> v \<in> varOfSent (forallSent (down N) paraForm)" ( is "?P N")
proof(induct_tac N)
  show "?P 0"
   by auto
   next
    fix N
   assume a1:"?P N" 
   show "?P (Suc N)"
   proof(rule impI)+
    (*have b0:"forallSent (Suc N # down ( N)) paraForm=cat (paraForm (Suc N)) (forallSent ( down ( N)) paraForm)" thm moreSent
       apply(rule moreSent)*)
    assume b0:"i \<le> Suc N" and b1:"  v \<in> varOfSent (paraForm i)"  
    have b2:"  varOfSent  (forallSent (down (Suc N)) paraForm) = varOfSent (paraForm (Suc N)) \<union>   varOfSent (forallSent (down N) paraForm)"
     by (metis down.simps(2) downNIsNotEmpty paraTheory.moreSent varsOnCat) 
     have "i \<le> N | i=Suc N" by(cut_tac b0,auto)
    moreover
    {assume c1:"i \<le> N"
     have c2:" v \<in>varOfSent (forallSent (down N) paraForm)" 
     apply(cut_tac c1 b1 a1,auto) done
     then have "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by(cut_tac c1 c2 b2,auto)
     }
     moreover
    {assume c1:"i =Suc N"
     from c1  have "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by(cut_tac c1 b1 b2,auto) 
     }
    ultimately show "v \<in> varOfSent (forallSent (down (Suc N)) paraForm)" by blast
  qed
 qed
     



lemma subByStatement1:
  assumes a1:"  x\<noteq> x' "
  shows "wellformedAssgnList (statement2Assigns ((parallel ( x', e) S)) ) \<longrightarrow>

  substFormByStatement (eqn (IVar  x) (Const n)) (parallel ( x', e) S)=  substFormByStatement  (eqn (IVar x) (Const n)) S"
  (is "?P S")
    

  apply(unfold substFormByStatement_def,simp)
  apply( induct_tac S)
  apply(cut_tac a1,unfold wellformedAssgnList_def, simp,auto)
  done





lemma ForallSentForm [simp]:
  shows a1:" (statement2Assigns (forallSent (down N)  (\<lambda>i. assign (Para n i, e' i))))=map (\<lambda>i. (Para n i, e' i)) (down N)" (is "?P N")
proof(induct_tac N)
  show "?P 0"
    apply simp
    done
next
  fix N
  assume b1:"?P N"
  show "?P (Suc N )"
  proof(cut_tac b1, simp)
    have b2:"\<exists> j xs. down N= j#xs"
      by (metis downNIsNotEmpty) 
  then obtain j xs where b2:"down N=j#xs" by blast
    show"  statement2Assigns (forallSent (Suc N # down N) (\<lambda>i. assign (Para n i, e' i))) = (Para n (Suc N), e' (Suc N)) # map (\<lambda>i. (Para n i, e' i)) (down N)"
      apply(cut_tac b1 b2,simp)
      done
  qed
qed

text{*lemma on valOf operator*}

lemma valOfLemma[simp]: "i \<le> N \<longrightarrow> (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=e i"
  apply(induct_tac N)
  apply simp
  apply auto
done        

lemma valOfLemma1Aux[simp]: "i > N \<longrightarrow> (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=  IVar (Para v i)"
  apply(induct_tac N)
  apply simp
  apply auto
done      


lemma valOfLemma1[simp,intro]: "i > N \<Longrightarrow> (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=  IVar (Para v i)"
  by (metis (lifting) valOfLemma1Aux)

lemma valOfLemma2Aux[simp]: "(var' \<notin> set (map fst xs)) \<longrightarrow> (valOf xs (var'))=IVar var'"
  apply(induct_tac xs)
  apply simp
  apply auto
done  

lemma valOfLemma2[simp,intro]: "(var' \<notin> set (map fst xs)) \<Longrightarrow> (valOf xs (var'))=IVar var'"
by (metis (lifting) valOfLemma2Aux)
  
lemma valOfLemma3 [simp]:"(\<forall> i.  var' \<noteq> Para v i) \<Longrightarrow>  (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) var')=IVar var'"
apply(rule valOfLemma2)
apply(induction N)
by auto

lemma valOfLemma4Aux :"v \<notin> set (map fst   (statement2Assigns S)) \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma4 [simp,intro]:"v \<notin> set (map fst   (statement2Assigns S)) \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
by (metis valOfLemma4Aux)

lemma valOfLemma5Aux :"( valOf (statement2Assigns   S ) v=IVar v) \<and>    ( valOf (statement2Assigns S') v=IVar v)\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) "
    proof(induct_tac S,auto)qed
    
lemma valOfLemma5 [simp,intro]:"( valOf (statement2Assigns   S ) v=IVar v) \<and>    ( valOf (statement2Assigns S') v=IVar v)  \<Longrightarrow> ( valOf (statement2Assigns  (cat S S')) v=IVar v) "
  by(metis  valOfLemma5Aux)
  
lemma valOfLemma6Aux :"( valOf (statement2Assigns   S ) v=IVar v) \<and>    ( valOf (statement2Assigns S') v=IVar v)\<longrightarrow>( valOf (statement2Assigns  (cat S S')) v=IVar v) "
    proof(induct_tac S,auto)qed
    
lemma varsOfNot [simp,dest!]:"v \<notin> set (map fst   (statement2Assigns S)) \<Longrightarrow>v \<in>set( map fst (statement2Assigns  (cat S S'))) = (v \<in> set (map fst   (statement2Assigns S'))) "
by (metis Un_iff varsOfSent1 varsOnCat)

lemma noEffectValOfStatementAux[intro]:
  shows "( v \<notin>  (varOfSent S) )\<longrightarrow> valOf (statement2Assigns  S)  v=IVar v" (is "?P N") 
 proof(induct_tac S,auto)qed
 
  lemma noEffectValOfStatement[simp,intro]:
  assumes "( v \<notin>  (varOfSent S)) "
  shows   "valOf (statement2Assigns  S)  v=IVar v" (is "?P N")
by (metis assms valOfLemma2Aux varsOfSent1) 
 
 lemma noEffectValOfForallStatementAux[intro]:
  shows "( \<forall>i. (v\<notin>  (varOfSent (ps i)) ))\<longrightarrow> valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v" (is "?P N")
  proof(induct_tac N)
    show "?P 0"
      apply simp
      done
   next
    fix N
    assume b1:"?P N"
    show "?P (Suc N)"
    proof(rule impI)
      assume c1:" \<forall>i. v \<notin> varOfSent (ps i)"
      show "valOf (statement2Assigns (forallSent (down (Suc N)) ps)) v = IVar v"
      proof(rule noEffectValOfStatement)
        have "   varOfSent (forallSent (down (Suc N)) ps) \<inter>{v} = {}"  thm forallVars
        proof(rule  forallVars,cut_tac c1,auto)qed
        then show   " v \<notin> varOfSent (forallSent (down (Suc N)) ps)"
        by (metis c1 forallVars1) 
      qed
  qed 
  qed
  
  
primrec andList::"formula list \<Rightarrow> formula" where
"andList [] = chaos" |
"andList (frm#frms) = andForm frm (andList frms)" 

lemma andList2Aux:
   shows "formEval (neg frm) s \<longrightarrow> frm \<in>set frms \<longrightarrow> formEval (neg (andList frms)) s"
   proof(induct_tac frms,auto)qed
   
lemma andList2:
   shows "formEval (neg frm) s \<Longrightarrow> frm \<in>set frms \<Longrightarrow> formEval (neg (andList frms)) s"
   by (metis andList2Aux)
   
lemma andList1Aux:
   shows "formEval ( (andList frms)) s  \<longrightarrow> frm \<in>set frms \<longrightarrow> formEval ( frm) s "
   proof(induct_tac frms,auto)qed
   
lemma andList1:
   shows "formEval ( (andList frms)) s  \<Longrightarrow>  frm \<in>set frms \<Longrightarrow> formEval ( frm) s " 
    by (metis andList1Aux)
lemma resAux1:
  assumes   b:"formEval frm s" and c:"formEval (neg (andList (frm#frms))) s"
  shows"formEval (neg (andList frms)) s"
  apply(cut_tac b c)
  apply auto
  done
  
  
lemma noEffectSubstAux:
  
  shows " (  (varOfExp e \<inter>  (varOfSent S) ={}) \<longrightarrow>(substExpByStatement e S)  =e) \<and>
           (  (varOfForm f \<inter>  (varOfSent S) ={} )\<longrightarrow> (substFormByStatement f S)  =  f )"
           
    (is "(( ?condOne e S\<longrightarrow> ?LHS e S=?RHS e S)\<and> (?condOnf f S\<longrightarrow> ?LHS1 f S=?RHS1 f S))")
  proof(induct_tac e and f)
      fix v
      let ?e="(IVar v)"
      show  "?condOne ?e S\<longrightarrow>?LHS ?e S=?RHS ?e S"
      proof(induct_tac S)
        fix prod
        let ?S="assign prod"
        show "?condOne ?e ?S \<longrightarrow>?LHS ?e ?S=?RHS ?e ?S"
        
        apply(unfold  substExpByStatement_def trans_def,auto)
        done
    next
       fix prod S
       let ?S="parallel prod S"
       assume b1:"?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
       
       show "?condOne ?e ?S \<longrightarrow> ?LHS ?e ?S=?RHS ?e ?S"
       
       proof(unfold  substExpByStatement_def trans_def,
       case_tac "fst prod =v",force)
       assume d1:"fst prod \<noteq> v "
       show "varOfExp (IVar v) \<inter> varOfSent (parallel prod S) = {} \<longrightarrow> (substExp (IVar v) (statement2Assigns (parallel prod S))) =
               (IVar v)"
       proof(cut_tac d1,simp) qed
      
      qed 
    qed 
next 
  fix n
  let ?e="(Const n)"
      show  "?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"
      apply( simp)
      done
next
  fix f e1 e2
  assume a1:" (?condOnf f S \<longrightarrow> ?LHS1 f S=?RHS1 f S)" and
  a2:"?condOne e1 S \<longrightarrow>?LHS e1 S=?RHS e1 S" and a3:"?condOne e2 S \<longrightarrow>?LHS e2 S=?RHS e2 S"
  let ?e="iteForm f e1 e2"
  show "?condOne ?e S \<longrightarrow>?LHS ?e S=?RHS ?e S"  
  proof(rule impI)
  assume b1:"?condOne ?e S"
  have c1:"?condOnf f S "
  apply(cut_tac b1,simp)
  by (metis bot_eq_sup_iff inf_sup_distrib2)
  have c2:"?condOne e1 S "
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
  have c3:"?condOne e2 S "
   apply(cut_tac b1,simp)
   by (metis c1 inf_bot_right inf_sup_absorb inf_sup_distrib2 sup_bot.left_neutral)
 with c1 c2 c3 a1 a2 a3
 show "?LHS ?e S=?RHS ?e S"
 by (metis substExpByStatement_def substExpite substFormByStatement_def)  
 qed 
 
next
  fix e1 e2
  
  assume a1:"?condOne e1 S \<longrightarrow>?LHS e1 S=?RHS e1 S" and a2:"?condOne e2 S \<longrightarrow>?LHS e2 S=?RHS e2 S"
  let ?f="eqn e1 e2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOne e1 S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 sup_eq_bot_iff)
  have c2:"?condOne e2 S"
  apply(cut_tac b1,simp)
   by (metis Int_Un_distrib2 sup_eq_bot_iff)
   with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
    by simp
   qed
next
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="andForm f1 f2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   qed
next
  fix f1
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)"
  let ?f="neg f1"
  show "( ?condOnf ?f S \<longrightarrow>?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  by(cut_tac b1,simp)
  
   with a1 c1
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   qed
 
next   
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="implyForm f1 f2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   
  qed
  
next
  let ?f="chaos"
  show "( ?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  by auto
next
  next   
  fix f1 f2
  assume a1:" (?condOnf f1 S \<longrightarrow> ?LHS1 f1 S=?RHS1 f1 S)" and  a2:" (?condOnf f2 S \<longrightarrow> ?LHS1 f2 S=?RHS1 f2 S)"
  let ?f="orForm f1 f2"
  
  show "(?condOnf ?f S \<longrightarrow> ?LHS1 ?f S=?RHS1 ?f S)"
  proof(rule impI)
  assume b1:"?condOnf ?f S"
  have c1:"?condOnf f1 S"
  apply(cut_tac b1,simp)
  by (metis Int_assoc inf_bot_right inf_sup_absorb)
   have c2:"?condOnf f2  S"
  apply(cut_tac b1,simp)
  by (metis Int_Un_distrib2 c1 sup_bot_left)
  with a1 a2 c1 c2 
   show "?LHS1 ?f S=?RHS1 ?f S"
   by auto
   
  qed
qed

lemma noEffectSubstExp [intro!]:
  
  shows " (  (varOfExp e \<inter>  (varOfSent S) ={}) \<Longrightarrow>(substExpByStatement e S)  =e) "
by (metis noEffectSubstAux)
  
lemma noEffectSubstForm [intro!]:
  
  shows " 
             (varOfForm f \<inter>  (varOfSent S) ={}) \<Longrightarrow> (substFormByStatement f S)  =  f "
 by (metis noEffectSubstAux) 
 
 
 thm noEffect
lemma  noEffectOnRule[simp,intro]:
  assumes a1:"  (varOfForm f \<inter>  (varOfSent (act r)) ={})"
  shows " invHoldForRule' s f r R "  (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
  have "?P2 s"
  using assms noEffectSubstForm by auto
  then show "?P1 s \<or> ?P2 s \<or> ?P3 s"
  by auto
qed 
  
lemma noEffectValOfForallStatement[simp,intro]:
  shows "( \<forall>i. (v \<notin>  (varOfSent (ps i))) ) \<Longrightarrow>  valOf (statement2Assigns  (forallSent (down N) ps)) v=IVar v" 
  by(metis noEffectValOfForallStatementAux)
  
 lemma noEffectValOfForallStatement1[simp,intro]:
  shows "( \<forall>i. (v \<notin>  (varOfSent (ps i))) ) \<Longrightarrow>  expEval ( valOf (statement2Assigns  (forallSent (down N) ps)) v) s=s  v"
by auto

lemma valOfLemma7Aux:"v \<notin> varOfSent S \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
proof(induct_tac S,auto)qed

lemma valOfLemma7 [simp,intro]:"v \<notin> varOfSent S \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S')) v"
by(metis valOfLemma7Aux)

lemma valOfLemma8Aux:"v \<in> varOfSent S \<longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v"
proof(induct_tac S,auto)qed

lemma valOfLemma8A[simp,intro]:"v \<in> varOfSent S \<Longrightarrow>( valOf (statement2Assigns  (cat S S')) v) =    ( valOf (statement2Assigns S)) v"
by(metis valOfLemma8Aux)


(*primrec wellGenStatement::"generalizeStatement \<Rightarrow> bool" where
"wellGenStatement (Parallel S) = wellformedAssgnList (map statement2Assigns S)" |
"wellGenStatement Skip =True" |
"wellGenStatement (If b S1 S2) = ((wellGenStatement S1) \<and> (wellGenStatement S2))"

lemma onWellFormedGenStatement:
  "wellGenStatement S \<longrightarrow> wellformedAssgnList (genStatement2Statements1 S)" (is "?P S")
  proof(induct_tac S)
  fix x
  show "?P (Parallel x)"
  by simp
next
  show "?P Skip" apply (simp,simp add:wellformedAssgnList_def) done
next
  fix b S1 S2
  assume a1:"?P S1" and a2:"?P S2" 
  let ?S ="If b S1 S2"
  show "?P ?S"
  proof
  assume b1:"wellGenStatement (generalizeStatement.If b S1 S2)"
  have b2:"wellGenStatement S1" by(cut_tac b1,simp)
  have b3:"wellGenStatement S2" by(cut_tac b1,simp)
  have b4:" wellformedAssgnList (genStatement2Statements1 S1)" using a1 b2 by auto
  have b5:" wellformedAssgnList (genStatement2Statements1 S2)" using a2 b3 by auto
  show "wellformedAssgnList (genStatement2Statements1 (generalizeStatement.If b S1 S2))"
  apply( cut_tac b4 b5, simp)*)


lemma  OnIfGenStatement: 
  (*assumes a1:"wellFormedGenStatement (If f S1 S2)" and a2:"formEval f s"*)
  shows "(formEval f s \<longrightarrow> transAux ( genStatement2Statements S1) s = transAux ( genStatement2Statements (If f S1 S2)) s )\<and>
        (\<not>formEval f s \<longrightarrow> transAux ( genStatement2Statements S2) s = transAux ( genStatement2Statements (If f S1 S2)) s)  " 
        (is "?P1 f S1 S2 \<and> ?P2 f S1 S2")
  proof(induct_tac S1  )
  fix S1
  let ?S1="Parallel S1"
  show "?P1 f ?S1 S2 \<and> ?P2 f ?S1 S2"
  proof(induct_tac S2 )  
    fix S2
    let ?S2="Parallel S2"
    show "?P1 f ?S1 ?S2 \<and> ?P2 f ?S1 ?S2"
    proof(case_tac "formEval f s")
      assume b1:"formEval f s"
      show "?P1 f ?S1 ?S2 \<and> ?P2 f ?S1 ?S2"
      proof(cut_tac b1,simp)
      show "transAux (map statement2Assigns S1) s =
    transAux
     (assignListVsAssignList f (map statement2Assigns S1) (map statement2Assigns S2)) s" (is "?Q S1 S2")
     proof(induct_tac S1)
        show "?Q [] S2"
        proof(induct_tac S2)
          show "?Q [] []" by auto 
        next
          fix a list
          assume c1:"?Q [] (list)"
          show "?Q [] (a#list)" 
          proof
            fix x
            show "transAux (map statement2Assigns []) s x =
            transAux (assignListVsAssignList f (map statement2Assigns []) (map statement2Assigns (a # list))) s x"
            (is "?R s x")
            proof - 
              have "(x =fst (statement2Assigns a)) \<or> (x\<noteq>fst (statement2Assigns a))" by blast
              moreover
              {assume e1:"(x =fst (statement2Assigns a))"
               have "?R s x"
               proof(cut_tac b1,simp,rule impI)
                  show " s x = transAux (rightMatch f (map statement2Assigns list)) s x" (is "?W list")
                  proof(induct_tac list)
                      show "?W []" by auto
                  next
                     fix a' list'
                     assume f1:"?W list'"
                     show "?W (a'#list')"
                     proof(cut_tac b1 f1,auto)qed
                  qed
                qed
                }
               moreover
              {assume e1:"(x \<noteq>fst (statement2Assigns a))"
               have "?R s x"
               proof(cut_tac b1,simp,rule impI)
                  show " s x = transAux (rightMatch f (map statement2Assigns list)) s x" (is "?W list")
                  proof(induct_tac list)
                      show "?W []" by auto
                  next
                     fix a' list'
                     assume f1:"?W list'"
                     show "?W (a'#list')"
                     proof(cut_tac b1 f1,auto)qed
                  qed
                qed
                }
              ultimately show "?R s x" by satx
           qed
         qed
       qed
    fix aS listS
    assume c1:"?Q listS S2"
    show "?Q (aS#listS) S2"
    proof
      fix x
      show "transAux (map statement2Assigns (aS # listS)) s x =
         transAux (assignListVsAssignList f (map statement2Assigns (aS # listS)) (map statement2Assigns S2)) s x" (is "?R S2")
      proof(case_tac "x= fst (statement2Assigns aS)")
        assume d1:"x= fst (statement2Assigns aS)"
         show "?R S2" apply (auto,simp add:Let_def)
lemma OnIfGenStatement:  
  assumes a1:"wellFormedGenStatement (If f S1 S2)" and a2:"formEval f s"
  shows "transAux ( genStatement2Statements S1) s = transAux ( genStatement2Statements (If f S1 S2)) s"


definition mapVarAux::"assignType list \<Rightarrow> assignType list  \<Rightarrow> formula \<Rightarrow> varType \<Rightarrow>assignType" where [simp]:
"mapVarAux L1 L2  f v \<equiv> 
  (let S12=(set (map fst L1)) \<inter> (set (map fst  L2)) in
   let S1'=(set (map fst L1))- S12 in
   let S2'=(set (map fst L2)) - S12 in
   if (v \<in> S12) then (v,iteForm f (valOf L1 v) (valOf L2 v))
   else if (v \<in> S1') then (v,valOf L1 v) 
   else if (v \<in> S2') then (v,valOf L2 v)
   else (v,(IVar  v )))"

primrec genStatement2Statements1::"generalizeStatement \<Rightarrow> assignType list" where
"genStatement2Statements1 (Parallel S) = map statement2Assigns S" | 
"genStatement2Statements1 (If b S1 S2) =
 ( let L1= genStatement2Statements1 S1 in
   let L2= genStatement2Statements1 S2 in
   map (mapVarAux L1 L2 b ) (List.union (map fst L1) (map fst L2)))"
 
  
definition stable::"circuit \<Rightarrow>  state \<Rightarrow>bool" where [simp]:
"stable M s \<equiv> \<forall>v e. assign (v,e) \<in> set (outputFun M) \<longrightarrow> (s v) =expEval  e s"

definition transOfCircuit::"circuit \<Rightarrow>state \<Rightarrow>state " where [simp]:
"transOfCircuit M s  \<equiv> ( trans (nextFun M) s)"

fun istrajOfCircuit::"circuit \<Rightarrow>state list \<Rightarrow> bool" where [simp]:
"istrajOfCircuit M [] = True"|
"istrajOfCircuit M [s] = stable M s" |
"istrajOfCircuit M (s#s'#sq) =(  stable M s \<and> s'=transOfCircuit M s \<and>istrajOfCircuit M (s'#sq))"


definition circuitSatGsteSpec::"circuit \<Rightarrow> gsteSpec \<Rightarrow>bool" where
"circuitSatGsteSpec M G \<equiv> \<forall> p sq. istrajOfCircuit M sq \<longrightarrow> isGstePath' p G
  \<longrightarrow> sqSatAssert sq p (antOf G) \<longrightarrow>   sqSatAssert sq p (consOf G)"
  
type_synonym nodeTagFunc="node \<Rightarrow> formula"  
  
definition consistent::"circuit \<Rightarrow> gsteSpec \<Rightarrow> nodeTagFunc \<Rightarrow> bool" where
"consistent M G tag \<equiv>( \<forall>e s s'. 
  (e \<in> edgesOf G \<longrightarrow> formEval (antOf G e) s \<longrightarrow> stable M s \<longrightarrow> stable M s'\<longrightarrow>
  s'=transOfCircuit M s \<longrightarrow> formEval (tag (source e)) s \<longrightarrow> formEval (tag (sink e)) s')) \<and>
  (\<forall>e s . (formEval (tag (source e)) s) \<longrightarrow> formEval (antOf G e) s \<longrightarrow>   formEval (consOf G e) s)"

type_synonym nodeTagFuncList="node \<Rightarrow> formula list"



primrec substExp :: "expType\<Rightarrow> assignType list \<Rightarrow>expType"  and 
substForm ::"formula \<Rightarrow> assignType list \<Rightarrow> formula" where 

substExpVar: "substExp  (IVar v') asgns=   (valOf  asgns v')  "| 

substExpConst: "substExp  (Const i)  asgns= Const i" |

substTop: "substExp top asgns=top" |

substUnkown: "substExp unKnown asgns=unKnown" |

substExpite: "substExp  (iteForm f e1 e2)  asgns= (iteForm (substForm f asgns) (substExp e1  asgns) (substExp e2  asgns))"
| 
"substForm (eqn l r)  asgns=(eqn (substExp l  asgns) (substExp r  asgns))"  |
"substForm ( andForm f1 f2)  asgns =   ( andForm (substForm f1  asgns)  (substForm f2  asgns))"|
"substForm (neg f1 )   asgns= (neg ( substForm f1  asgns ))"|
"substForm (orForm f1 f2)   asgns= ( orForm (substForm f1  asgns )  (substForm f2  asgns))"|
"substForm (implyForm f1 f2)   asgns= (implyForm (substForm f1 asgns)  (substForm f2  asgns))" |
"substForm  chaos   asgns=chaos"

definition  instExp ::"expType \<Rightarrow>circuit \<Rightarrow>expType"   where [simp]:
"instExp e M\<equiv>substExp e ((map statement2Assigns (outputFun M)))" 

definition instCond ::"formula \<Rightarrow>circuit \<Rightarrow>formula"   where [simp]:
"instCond f M\<equiv>substForm f ((map statement2Assigns (outputFun M)))"  


definition preCond ::" formula \<Rightarrow> circuit \<Rightarrow>formula" where [simp]:
"preCond f  M \<equiv> substForm f ((map statement2Assigns (nextFun M)))  "

definition preExp ::" expType \<Rightarrow> circuit \<Rightarrow>expType" where [simp]:
"preExp e  M \<equiv> substExp e ((map statement2Assigns (nextFun M)))  "

(*lemma condInst:
  assumes a1:"stable M s" and a2:"wellDefinedCircuit M" and a3:"M=Circuit inputs regs outs outf nf"
  shows "expEval (instExp e M) s =expEval e s \<and>
         formEval (instCond f M) s = formEval f s "
         (is "((  ?LHS e M=?RHS e M)\<and> ( ?LHS1 f M=?RHS1 f M))")        
  proof(induct_tac e and f)
  fix v
  let ?e="(IVar v)"
  show  "?LHS ?e M=?RHS ?e M"
  proof(case_tac "x \<in> outputsOf M")
     assume b1:"x \<in> outputsOf M"
     show  "?LHS ?e M=?RHS ?e M"
     apply(cut_tac a1 a2 a3 b1,simp) *) 
primrec assignVsAssignList::"formula\<Rightarrow> assignType \<Rightarrow> assignType list \<Rightarrow>assignType \<times>assignType list" where
"assignVsAssignList f asgn [] =((fst asgn, (iteForm f (snd asgn) (IVar (fst asgn)))),[])" |
"assignVsAssignList f asgn (asgn'#asgns) =
  (if ((fst asgn) = (fst asgn')) 
   then (((fst asgn),(iteForm f (snd asgn) (snd asgn'))), asgns) 
   else (let mid=assignVsAssignList f asgn asgns in
          (fst mid, asgn'#(snd mid))))"

primrec rightMatch::"formula \<Rightarrow> assignType list \<Rightarrow>assignType list" where
"rightMatch f [] =[]" |
"rightMatch f (asgn # asgns) = (fst asgn, (iteForm f  (IVar (fst asgn)) (snd asgn)))#(rightMatch f asgns)"

primrec assignListVsAssignList::"formula\<Rightarrow> assignType list \<Rightarrow> assignType list \<Rightarrow>assignType list" where
"assignListVsAssignList f [] asgns =rightMatch f asgns"|
"assignListVsAssignList f (asgn#asgnsL) asgnsR =
  (let mid=assignVsAssignList f asgn asgnsR in
   let mid2=assignListVsAssignList f asgnsL (snd mid) in
   ((fst mid)#mid2))"
   
primrec genStatement2Statements::"generalizeStatement\<Rightarrow> assignType list" where
"genStatement2Statements (Parallel S) = map statement2Assigns S" | 
"genStatement2Statements (If b S1 S2) =
 ( let L1= genStatement2Statements S1 in
   let L2= genStatement2Statements S2 in
    (assignListVsAssignList b L1 L2))"


primrec substExp :: "expType\<Rightarrow> assignType list \<Rightarrow>expType"  and 
substForm ::"formula \<Rightarrow> assignType list \<Rightarrow> formula" where 

substExpVar: "substExp  (IVar v') asgns=   (valOf  asgns v')  "| 

substExpConst: "substExp  (Const i)  asgns= Const i" |

substTop: "substExp top asgns=top" |

substUnkown: "substExp unKnown asgns=unKnown" |

substExpite: "substExp  (iteForm f e1 e2)  asgns= (iteForm (substForm f asgns) (substExp e1  asgns) (substExp e2  asgns))"
| 
"substForm (eqn l r)  asgns=(eqn (substExp l  asgns) (substExp r  asgns))"  |
"substForm ( andForm f1 f2)  asgns =   ( andForm (substForm f1  asgns)  (substForm f2  asgns))"|
"substForm (neg f1 )   asgns= (neg ( substForm f1  asgns ))"|
"substForm (orForm f1 f2)   asgns= ( orForm (substForm f1  asgns )  (substForm f2  asgns))"|
"substForm (implyForm f1 f2)   asgns= (implyForm (substForm f1 asgns)  (substForm f2  asgns))" |
"substForm  chaos   asgns=chaos


(*primrec wellDefined:: "generalizeStatement1 \<Rightarrow> varType set \<Rightarrow> varType set \<Rightarrow> bool" where
" wellDefined (Parallel ps)  inputs regs = 
"wellDefinedCircuit1 (Circuit1 inputs regs  nf) =
(((set inputs) \<inter> (set  regs) = {}) 
  \<and> (\<forall> \<alpha>. (\<alpha> \<in> set nf) \<longrightarrow> ( (assignedVar \<alpha>) \<in>  set regs ))
  \<and> (\<forall> \<alpha>. (\<alpha> \<in> set nf)\<longrightarrow> ((varOfExp (assignedExp \<alpha>)) \<subseteq> set (regs@inputs) ))
  \<and> (distinct (map assignedVar nf)) 
   )"

primrec wellDefinedCircuit1:: "circuit1 \<Rightarrow> bool" where
"wellDefinedCircuit1 (Circuit1 inputs regs  nf) =
(((set inputs) \<inter> (set  regs) = {}) 
  \<and> (\<forall> \<alpha>. (\<alpha> \<in> set nf) \<longrightarrow> ( (assignedVar \<alpha>) \<in>  set regs ))
  \<and> (\<forall> \<alpha>. (\<alpha> \<in> set nf)\<longrightarrow> ((varOfExp (assignedExp \<alpha>)) \<subseteq> set (regs@inputs) ))
  \<and> (distinct (map assignedVar nf)) 
   )"*)

end
