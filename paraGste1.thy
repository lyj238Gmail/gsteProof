theory paraGste1 imports Main Finite_Set
begin

section{*Variables and values*}

text{*
According to the aforementioned discussion in section ?, firstly we define the variables used in the protocols. 
There are two kinds of variables, global and parameterized (local) 
variables. In hardware implemetations of the protocols, 
the variables are implenteed as registers in global or local modules. *}

datatype varType=Ident  string | Para varType  nat |Field  varType   string 

datatype scalrValueType=enum string string |index nat | boolV bool | topVal | bottomVal

(*datatype inVar = Input varType   
  
datatype regVar= Reg varType*)

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
down0:"down 0=[0]" |
downSuc:"down (Suc n)=Suc n #(down n)"
 

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

primrec caseExp::"formulaExpPair list  \<Rightarrow> expType" where
 caseNil: "caseExp [] = unKnown"|
 caseTail:"caseExp (gp # tls) =iteForm (fst gp) (snd gp) (caseExp tls )"
 
 

 
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
   
text{*Variables of a variable, an expression, a formula, and a statement is defined by
varsOfVar, varOfExp, varOfForm and varOfSent respectively*}


primrec varOfExp::"expType \<Rightarrow> varType list"  and
  varOfForm::"formula \<Rightarrow> varType list"  where 

"varOfExp  (IVar v) = [ v]" |
"varOfExp   (Const j) =  []" |

"varOfExp   (iteForm f e1 e2) =(varOfForm f) @  (varOfExp   e1 )  @   (varOfExp  e2)" |
"varOfExp   (uif f es) = (concat (map varOfExp es))"|
"varOfExp   (top) =  []" |
"varOfExp   (unKnown) =  []" |

"varOfForm   (eqn e1 e2) = ( (varOfExp   e1 )  @   (varOfExp  e2))" |
"varOfForm   ( andForm f1 f2) =(  (varOfForm  f1 ) @  (varOfForm  f2 ))"|
"varOfForm   (neg f1 ) = (  (varOfForm   f1 ))"|
"varOfForm   (orForm f1 f2) =(  (varOfForm   f1 )   @   (varOfForm  f2 ))"|
"varOfForm   (implyForm f1 f2) = (  (varOfForm  f1 ) @ (varOfForm f2 ))"|
"varOfForm   (uip p es) = (concat (map varOfExp es))"|
"varOfForm   (chaos) =[]"
 

primrec  varOfSent::"statement \<Rightarrow> varType list" where
" varOfSent  (assign a)=[  (fst a)] " 


datatype generalizeStatement1= Parallel1 "generalizeStatement1 list"  |
   If1 formula generalizeStatement1 generalizeStatement1 |
   AtomStatement statement
   
fun assignedVars::"generalizeStatement1 \<Rightarrow>varType set" where
"assignedVars (Parallel1 []) = {}"|
"assignedVars (Parallel1 (s#ss)) = (assignedVars s) \<union> assignedVars (Parallel1 ss) "|
"assignedVars (If1 b S1 S2) =(assignedVars S1) \<union> (assignedVars S2) "| 
"assignedVars (AtomStatement S) = {assignedVar S}"

definition writeArr::"varType \<Rightarrow> nat \<Rightarrow>expType \<Rightarrow>expType\<Rightarrow>statement list" where
"writeArr a bound adre ce \<equiv> map  
   (\<lambda>i. assign ((Para a i), iteForm (eqn adre (Const (index i))) ce (IVar (Para a i))))
   (down bound)"

type_synonym formulaStatementPair ="formula \<times> generalizeStatement"

abbreviation skip::" generalizeStatement" where
"skip \<equiv> Parallel []"

fun caseStatement::"formulaStatementPair list  \<Rightarrow> generalizeStatement" where
  caseStatement1:"caseStatement [gp] =If  (fst gp) (snd gp) skip"|
  caseStatement2:"caseStatement (gp # tls) =If (fst gp) (snd gp) (caseStatement tls )"

definition writeArr'::"varType \<Rightarrow> nat \<Rightarrow>expType \<Rightarrow>expType\<Rightarrow> generalizeStatement"  where [simp]:
"writeArr' a bound adre  ce\<equiv> caseStatement 
(map  (\<lambda>i. ((eqn adre (Const (index i))),Parallel [assign ((Para a i), ce)])) (down bound))"
 

text{*With the formalizatiion of formula and statement, it is natural to define a rule. A guard and
 statement of a rule are also defined for convenience. *}
 
section{*gste graph*} 
 
datatype node= Vertex nat

datatype  edge=Edge node  node 

type_synonym edgeToForm =  "edge \<Rightarrow>  formula"

datatype gsteSpec= Graph  node  "edge list" edgeToForm edgeToForm

primrec  antOf::"gsteSpec \<Rightarrow> edge \<Rightarrow> formula" where
antOf_def: "antOf  (Graph  init  edges ant conss) e = ant e"

primrec consOf::"gsteSpec \<Rightarrow>edge \<Rightarrow> formula" where
"consOf  (Graph  init  edges ant conss) e  = conss e"

primrec source::"edge \<Rightarrow> node" where
"source (Edge n1 n2) = n1"

primrec sink::"edge \<Rightarrow> node" where
"sink (Edge n1 n2) = n2"

primrec edgesOf ::"gsteSpec  \<Rightarrow>  edge set" where 
"edgesOf  (Graph  init  edges ant conss) = set edges   "
 

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
"isGstePath' p G \<equiv>(isPathOf' p G \<and>( \<not>( p=[]) \<longrightarrow> source ( hd p)=initOf G))"

section{*semantics of a protocol*}
text{*A  state of a protocol  is an instantaneous snapshot of its  behaviour given by an assignment of  values to variables of
the circuit. Therefore, we define:*}

type_synonym state= "varType \<Rightarrow> scalrValueType "


datatype  circuit=Circuit "varType list" "varType list" "varType list" "statement list"  "statement list"


definition varsOfVar::" varType \<Rightarrow> varType set"  where  [simp]:
" varsOfVar x  = {x}" 



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

fun genTrans1::"generalizeStatement1\<Rightarrow> interpretFunType  \<Rightarrow> state \<Rightarrow>state " where 
"genTrans1 (AtomStatement (assign as)) I s x= (s((fst as) :=  expEval I (snd as) s)) x"|
"genTrans1 (Parallel1 []) I s x= s x" |
"genTrans1 (Parallel1 (S#ss)) I s x= (if (x \<in> (assignedVars S)) then genTrans1  S  I s x else genTrans1 (Parallel1 ss) I s x) " |
"genTrans1 (If1 b S1 S2) I s x=(if (formEval I b s) then (genTrans1  S1 I s x) else  (genTrans1 S2 I s x))"


definition transOfCircuit2::"generalizeStatement1 \<Rightarrow>interpretFunType \<Rightarrow>state \<Rightarrow>state " where [simp]:
"transOfCircuit2 M I s  \<equiv> (genTrans1 M I s)"

definition transOfCircuit1::"generalizeStatement \<Rightarrow>interpretFunType \<Rightarrow>state \<Rightarrow>state " where [simp]:
"transOfCircuit1 M I s  \<equiv> (genTrans M I s)"

fun istrajOfCircuit1::"generalizeStatement\<Rightarrow> interpretFunType \<Rightarrow> state list \<Rightarrow> bool" where [simp]:
"istrajOfCircuit1 M I [] = True"|
"istrajOfCircuit1 M I [s] = True" |
"istrajOfCircuit1 M I (s#s'#sq) =(   s'=transOfCircuit1 M I  s \<and>istrajOfCircuit1 M I (s'#sq))"


definition circuitSatGsteSpec1::"generalizeStatement \<Rightarrow> gsteSpec \<Rightarrow>  interpretFunType \<Rightarrow>bool" where
"circuitSatGsteSpec1 M G I\<equiv> \<forall> p sq. istrajOfCircuit1 M I sq \<longrightarrow> isGstePath' p G \<longrightarrow> (length p= length sq)
  \<longrightarrow> sqSatAssert I sq p (antOf G) \<longrightarrow>   sqSatAssert I sq p (consOf G)"
  
type_synonym nodeTagFunc="node \<Rightarrow> formula"
  
definition consistent1::"generalizeStatement \<Rightarrow> interpretFunType  \<Rightarrow> gsteSpec \<Rightarrow> nodeTagFunc \<Rightarrow> bool" where
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
"preCond1 f (Parallel S)  = substForm f (map statement2Assigns S) " |
"preCond1 f  (If b S1 S2) = orForm (andForm b (preCond1 f  S1)) (andForm (neg b) (preCond1 f  S2))"


primrec  preExp1 ::" expType \<Rightarrow>  generalizeStatement  \<Rightarrow>expType" where [simp]:
"preExp1 e  (Parallel S)  = substExp e (map statement2Assigns S)  " |
"preExp1 e   (If b S1 S2) = iteForm b (preExp1 e S1) (preExp1 e S2)"


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

definition consistent'::"generalizeStatement \<Rightarrow> interpretFunType \<Rightarrow> gsteSpec \<Rightarrow> nodeTagFuncList \<Rightarrow> bool" where [simp]:
"consistent' M I G tag \<equiv>( \<forall>e. 
  (e \<in> edgesOf G \<longrightarrow> 
  (let f=andListForm (tag (sink e)) in
   let f'=andListForm (tag (source e)) in
  tautlogy (implyForm (andForm f' (antOf G e)) (preCond1  f    M )) I)))"
 

fun sqSatTagFunc::"state list \<Rightarrow> interpretFunType\<Rightarrow> edge list\<Rightarrow>nodeTagFuncList\<Rightarrow> bool" where [simp]:
"sqSatTagFunc [] I [] tag = True"|
"sqSatTagFunc (s#sq) I [] tag = False"|
"sqSatTagFunc [] I (e#es) tag = False"|
"sqSatTagFunc (s#sq) I (e#es) tag= 
       ((sqSatTagFunc sq I es tag) \<and> formEval I (andListForm (tag (source e)))  s
       )"

lemma sqSatConsisitentGraph:
  assumes a1:"consistent' M I G tag"  
  shows "e \<in> edgesOf G \<longrightarrow> 
  formEval I (andListForm (tag (source e))) s\<longrightarrow> formEval I(antOf G e) s \<longrightarrow>
  formEval I (andListForm (tag (sink e))) (genTrans M I s)"
  proof(rule impI)+
   assume b1:"e \<in> edgesOf G" and b2:"formEval I (andListForm (tag (source e))) s" and
   b3:" formEval I (antOf G e) s"   
   let ?f="andListForm (tag (sink e))"  let ?f'="andListForm (tag (source e))"
   from a1  b1  have b6:
    " tautlogy (implyForm (andForm ?f' (antOf G e)) (preCond1 ?f  M)) I "
    by (unfold consistent'_def, auto simp add:Let_def)
   
   have b5:"formEval I (preCond1 ?f  M) s"
   proof -
    from a1  b1  have b6:
    " tautlogy (implyForm (andForm ?f' (antOf G e)) (preCond1 ?f  M)) I "
    by (unfold consistent'_def, auto simp add:Let_def)
    show b5:"formEval I (preCond1 ?f  M) s"
    using b2 b3 b6 by auto
   
  qed
  show "formEval I (andListForm (tag (sink e))) (genTrans M I s)"
  using  b5 lemmaOnPre by blast
 qed


 
lemma consistentLemmaAux:
  assumes a1:"consistent' M I G tag"  
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
      (* have d9:"(varOfForm (andListForm (tag (sink e)))) \<subseteq> (regsOf1 M)" using a4 d8 by auto*)
       have d10:"formEval I  (andListForm (tag (sink e))) (genTrans M I s)"
       using a1  c6 d7 d8  sqSatConsisitentGraph by blast 
       have d11:"source (hd p) = sink e" using c5 d2 c4 by auto
       have d12:"(transOfCircuit1 M I s) =(hd sq')" using c3 d1 c5 apply auto done
       have d13:"formEval I (andListForm (tag (source (hd p)))) (hd sq') "
       using  d10 d11 d12 by auto 
       have d14:"isPathOf' p G" using c4 by auto
       have d15:"sqSatTagFunc sq' I p tag" using b1 d3 d13 d4 c4 c5 d14 d6 by auto
       }
      ultimately show "sqSatTagFunc sq' I p tag" by auto
    next
      show "formEval I (andListForm (tag (source e))) s" using c6 by auto
  qed
 qed
qed

lemma consistentLemma:
  assumes a1:"consistent' M I G tag"  and
  a2:"istrajOfCircuit1 M I sq " and a3:"formEval I (andListForm (tag (source (hd p)))) (hd sq)"
    and a4:"length p = length sq" and a5:" sqSatAssert I sq p (antOf G)" and a6:"\<not>( p=[])"
    and a7:"isPathOf' p G "
  shows " sqSatTagFunc sq I p tag  " (is " ?P p")
using a2 a3 a4 a5 a7 consistentLemmaAux local.a1 by blast
  
lemma andListNilIsCHAOS:
  "formEval  I (andListForm []) s"
  by auto
  
definition circuitSatGsteSpecAux::"generalizeStatement \<Rightarrow> gsteSpec \<Rightarrow>  interpretFunType 
\<Rightarrow>state list \<Rightarrow>edge list\<Rightarrow>nodeTagFuncList \<Rightarrow>bool" where [simp]:
"circuitSatGsteSpecAux M G I sq p tag\<equiv> istrajOfCircuit1 M I sq \<longrightarrow> isPathOf' p G \<longrightarrow> (length p= length sq) \<longrightarrow>
   formEval I (andListForm (tag (source (hd p)))) (hd sq)\<longrightarrow> sqSatAssert I sq p (antOf G) \<longrightarrow>   sqSatAssert I sq p (consOf G)"  
  
lemma mainLemmaAux:
  assumes a1:"consistent' M I G tag" and 
  a2:"\<forall> e. e \<in>edgesOf G\<longrightarrow> tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) I"  
   
  shows "\<forall>p. circuitSatGsteSpecAux M G I sq p tag" (is "?P sq")
  proof(induct_tac sq)
    show "?P []" by auto
    next
    fix s sq
    
    assume b0:"?P sq"
    
    show "?P (s#sq)"    
    proof(unfold circuitSatGsteSpecAux_def,rule allI,(rule impI)+)
      fix p0
      
      assume b1:"istrajOfCircuit1 M I  (s # sq) "
      and b3:"length p0 = length (s # sq) " and
      b4:" sqSatAssert I  (s # sq) p0 (antOf G)" and
      b2:"formEval I (andListForm (tag (source (hd p0)))) (hd (s # sq))"  
      and b5:" isPathOf' p0 G "
      have b60:"\<exists> e p. p0=e#p"        
        by (metis b3 hd_Cons_tl length_greater_0_conv list.distinct(1))
      then obtain e and p where  b6:"p0= e #p" by blast 
      have  c1:"istrajOfCircuit1 M I  (  sq) "
          apply(cut_tac b1 ,case_tac sq,auto)  done
      have c3:"length p= length sq"
          apply(cut_tac b3 b6,auto) done
      
      have c4:"sqSatAssert I sq p (antOf G) \<and>   formEval I (antOf G e) s "
      proof(cut_tac b4 b6,auto) qed
      have c5:"isPathOf' p G \<and> e\<in> edgesOf G" by(cut_tac b5 b6,auto)
      
      show " sqSatAssert I  (s # sq)  p0 (consOf G)"
      proof(cut_tac b6,simp,rule conjI)
        
        show " sqSatAssert I sq p (consOf G)"
        proof(case_tac p)
          assume d1:"p=[]"
          have d2:"sq=[]" apply(cut_tac b6 b3,auto)
            by (simp add: d1)
          show " sqSatAssert I sq p (consOf G)" by(cut_tac d1 d2,auto)
          next
          fix e' p'
          assume d1:"p=e'#p'"
            have d2:"length p=length sq" by(cut_tac b6 b3,auto)
            have d6:"sqSatTagFunc (s#sq) I p0 tag"
            using b1 b2 b3 b4 b5 consistentLemmaAux local.a1 by blast
       
            then have d6:"formEval I (andListForm (tag (source (hd p)))) (hd ( sq))"  
              apply(cut_tac b5  b6,auto,cut_tac d1,simp)
              by (metis d1 d2 hd_Cons_tl length_greater_0_conv list.distinct(1) sqSatTagFunc.simps(4))
            show " sqSatAssert I sq p (consOf G)"
            using b0 c1 c4 c5 circuitSatGsteSpecAux_def d2 d6 by blast 
         qed
   next
   show "formEval I (consOf G e) s"
    apply(cut_tac a2 b6 b2 c4 c5,simp)
   done
   qed 
 qed
qed

definition circuitSatGsteSpec::"generalizeStatement \<Rightarrow> gsteSpec \<Rightarrow>  interpretFunType \<Rightarrow>bool" where
"circuitSatGsteSpec M G I\<equiv> \<forall> p sq. istrajOfCircuit1 M I sq \<longrightarrow> isGstePath' p G \<longrightarrow> (length p= length sq)
  \<longrightarrow> sqSatAssert I sq p (antOf G) \<longrightarrow>   sqSatAssert I sq p (consOf G)"  

lemma mainLemma:
  assumes a1:"consistent' M I G tag" and 
  a2:"\<forall> e. e \<in>edgesOf G\<longrightarrow> tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) I"  and
  a3:"tag (initOf G) =[]" 
  shows " circuitSatGsteSpec M G I " (is "?P sq")
proof(unfold circuitSatGsteSpec_def,(rule allI)+,(rule impI)+)  
  fix p sq
  assume b1:"istrajOfCircuit1 M I sq" and
  b2:"isGstePath' p G" and b3:" length p = length sq" and b4:" sqSatAssert I sq p (antOf G) "
  have b5:"\<forall>p. circuitSatGsteSpecAux M G I sq p tag"
    using a2 local.a1 mainLemmaAux by blast
  have b6:"isPathOf' p G \<and>( \<not>( p=[]) \<longrightarrow> source ( hd p)=initOf G)"  
    by(cut_tac b2,unfold  isGstePath'_def,auto) 
  have b7:" \<not>( p=[]) \<longrightarrow>formEval I (andListForm (tag (source (hd p)))) (hd sq)"
    by(cut_tac a3 b6,auto)
  show "sqSatAssert I sq p (consOf G)"
  proof(case_tac "p=[]")
    assume c1:"p=[]"
    show "sqSatAssert I sq p (consOf G)" by(cut_tac c1 b3,auto)
  next
    assume c1:"p\<noteq>[]"    
    have b8:" source ( hd p)=initOf G"  
      by(cut_tac c1 b6,auto) 
    have b9:" formEval I (andListForm (tag (source (hd p)))) (hd sq)"
      by(cut_tac c1 b7,auto)
    show "sqSatAssert I sq p (consOf G)"
      using b1 b3 b4 b5 b6 b9 circuitSatGsteSpecAux_def by blast
  qed
qed

lemma OnIfPos:
  assumes a1:"formEval I b s" 
  shows "formEval I (preCond1 f (If b S1 S2)) s=formEval I (preCond1 f  S1 ) s" 
    by (cut_tac a1,auto)
    
lemma OnIfNeg:
  assumes a1:"formEval I (neg b) s" 
  shows "formEval I (preCond1 f (If b S1 S2)) s=formEval I (preCond1 f  S2 ) s" 
    by (cut_tac a1,auto)    
    
subsection{*more lemmas on valOf operator*}

text{*more lemmas on valOf operator*}

lemma valOfLemmaAux[simp]: "i \<le> N \<longrightarrow> (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=e i"
  apply(induct_tac N)
  apply simp
  apply auto
done  


lemma valOfLemma[simp]: "i \<le> N \<Longrightarrow> (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=e i"
by (metis valOfLemmaAux ) 

lemma valOfLemma2Aux[simp]: "(var' \<notin> set (map fst xs)) \<longrightarrow> (valOf xs (var'))=IVar var'"
  apply(induct_tac xs)
  apply simp
  apply auto
done  

lemma valOfLemma2[simp,intro]: "(var' \<notin> set (map fst xs)) \<Longrightarrow> (valOf xs (var'))=IVar var'"
by (metis (lifting) valOfLemma2Aux)
  
lemma valOfLemma3 [simp]:"(\<forall> i.  var' \<noteq> Para v i) \<Longrightarrow> 
(valOf (map (\<lambda>i. (Para v i, e i)) (down N)) var')=IVar var'"
apply(rule valOfLemma2)
apply(induction N)
by auto

lemma valOfLemma4Aux :"v \<notin> set (map fst   (map statement2Assigns S)) \<longrightarrow>
( valOf (map statement2Assigns  ( S@ S')) v) =    ( valOf (map statement2Assigns S')) v"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma4 [simp,intro]:"v \<notin> set (map fst   (map statement2Assigns S)) \<Longrightarrow>
( valOf (map statement2Assigns  ( S@ S')) v) =    ( valOf (map statement2Assigns S')) v"
by (metis valOfLemma4Aux)

lemma valOfLemma5Aux :"v \<notin> set (map fst  As') \<longrightarrow>
( valOf (As'@ As) v) =    ( valOf As) v"
    proof(induct_tac As',auto)qed

lemma valOfLemma5 :"v \<notin> set (map fst  As') \<Longrightarrow>
( valOf (As'@ As) v) =    ( valOf As) v"
   by (metis valOfLemma5Aux)  
   
lemma mapFstAssignsAux:"(\<forall> i.  v' \<noteq> Para v i) \<longrightarrow> v' \<notin> set (map fst ( map (statement2Assigns o 
                      (\<lambda>i. assign (Para v i,  e i))) L )) "
  apply(induct_tac L,auto) done              
  
lemma mapFstAssigns [simp,intro]:"(\<forall> i.  v' \<noteq> Para v i) \<Longrightarrow> v' \<notin> set (map fst ( map (statement2Assigns o 
                      (\<lambda>i. assign (Para v i,  e i))) L )) "
  apply(metis mapFstAssignsAux) done
  
lemma valOfLemma6Aux :"v \<notin> set (map fst   S) \<longrightarrow>
( valOf  ( S@ S') v) =    ( valOf   S') v"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma6 [simp,intro!]:"v \<notin> set (map fst   S) \<Longrightarrow>
( valOf  ( S@ S') v) =    ( valOf   S') v"
by (metis valOfLemma6Aux)



lemma valOfLemma7 [simp]:
"map (statement2Assigns \<circ>
                      (\<lambda>i. assign (Para v i, e i)))
                  [0..<depth] = map (\<lambda>i.   (Para v i, e i)) [0..<depth]" 
apply(induct_tac depth)
apply auto
done

lemma valOfLemma8 [simp]:
"map (statement2Assigns \<circ>
                      (\<lambda>i. assign (Para v i, e i)))
                  (down Last) = map (\<lambda>i.   (Para v i, e i)) (down Last)" 
apply(induct_tac Last)
apply auto
done

lemma valOfLemma9[simp]:
"\<forall>ASL. valOf (map (\<lambda>i.   (Para v i, e i)) [0..<depth]@ASL) (Ident v') =valOf ASL (Ident v')" (is "?P depth")
proof(induct_tac depth)
  show "?P 0"
    by auto
next 
  fix n
  assume a1:"?P n"
  
  show "?P (Suc n)"
  proof 
    fix ASL
    have a2:"(map (\<lambda>i. (Para v i, e i)) [0..<Suc n] @ ASL) =
    (map (\<lambda>i. (Para v i, e i)) [0..< n]) @((Para v ( n), e ( n))#ASL)"
    apply auto done
    have a3:" valOf ((map (\<lambda>i. (Para v i, e i)) [0..< n]) @((Para v ( n), e ( n))#ASL)) (Ident v') = 
    valOf  ((Para v ( n), e ( n))#ASL) (Ident v')"
    by (simp add: local.a1)
    
    show "valOf (map (\<lambda>i. (Para v i, e i)) [0..<Suc n] @ ASL) (Ident v') = valOf ASL (Ident v')"
      apply(cut_tac a2 a3,auto)
   done
   qed
 qed

lemma valOfLemma10:"
          valOf (map (statement2Assigns \<circ>
                       (\<lambda>i. assign (Para (Ident ''mem'') i,
                                    iteForm (eqn (Const (index i)) (Const (index 0))) dataIn
                                     (caseExp
                                       (map (\<lambda>ia. (eqn (uif ''-'' [Const (index i), Const (index (Suc 0))]) (Const (index ia)), mem ia))
                                         (down depth))))))
                   [0..<depth] @
                  [(Ident ''tail'', iteForm (neg (eqn emptyFifo LOW)) (uif ''+'' [tail, Const (index (Suc 0))]) tail),
                   (Ident ''empty'', LOW)])
            (Ident ''tail'') = iteForm (neg (eqn emptyFifo LOW)) (uif ''+'' [tail, Const (index (Suc 0))]) tail"
     by auto  
     
lemma valOfLemma11[simp]: "i \<le> N \<longrightarrow> (valOf (map (\<lambda>i. (Para v i, e i)) (down N)) (Para v i))=e i"
  apply(induct_tac N)
  apply simp
  apply auto
done 

lemma substMap:
 
shows "(\<forall> x. x \<in> set xs \<longrightarrow> substExp  x f=x)\<longrightarrow>substExp  (uif fStr xs) f =uif fStr xs"
proof(induct_tac xs,auto) qed

lemma substNIl: 
  shows "(substExp e [] = e) \<and> (substForm f [] =f)"
  using substMap by(induct_tac e and f,auto)
  
  
lemma substNIlForm[simp]: 
  shows " (substForm f [] =f)"
by (simp add: substNIl)
 
lemma substNIlExp[simp]: 
  shows " (substExp e [] =e)"
by (simp add: substNIl) 
  
lemma tautologyImplTrans[intro!]:
  assumes a1:"tautlogy (implyForm P Q) I" and a2:"tautlogy (implyForm  Q R) I"
  shows "tautlogy (implyForm P R) I"
using a2 local.a1 by auto 

lemma noEffectSubstAux:
  
  shows " (  (v \<notin>set (varOfExp e) ) \<longrightarrow>  substExp  e ((v,e')#S)  =substExp  e S) \<and>
          (  (v \<notin>set (varOfForm f)  )\<longrightarrow> substForm f ((v,e')#S)  =  substForm f S )"
           
    (is "(( ?condOne e S\<longrightarrow> ?LHS e S=?RHS e S)\<and> (?condOnf f S\<longrightarrow> ?LHS1 f S=?RHS1 f S))")
  proof(induct_tac e and f,auto)qed
  

lemma noEffectSubstExp [simp,intro!]:
  
  shows " v \<notin>set (varOfExp e)  \<Longrightarrow>  substExp  e ((v,e')#S)  =substExp  e S "
by (metis noEffectSubstAux)
  
lemma noEffectSubstForm [simp,intro!]:
  
  shows "    (v \<notin>set (varOfForm f)  \<Longrightarrow>  substForm f ((v,e')#S)  =  substForm f S ) "
 by (metis noEffectSubstAux) 
 
 lemma noEffectSubstAllAux:
  
  shows " (  (set (varOfExp e) \<inter> set (map fst S) ={} ) \<longrightarrow>  substExp  e S  = e) \<and>
          (  (set (varOfForm f) \<inter> set (map fst S) ={} )\<longrightarrow> substForm f S =  f )"
           
    (is "?P S")
  proof(induct_tac S,simp)
  fix a S
    assume a1:"?P S"
    show "?P (a#S)" (is "?P1 \<and> ?P2")
    proof(rule conjI)
    show "?P1"
    proof
      assume b1:" set (varOfExp e) \<inter> set (map fst (a # S)) = {}"
      have b2:"set (varOfExp e) \<inter> set (map fst S) ={}" by(cut_tac b1,auto)
      have b3:" substExp  e (a # S) = substExp  e S" 
      proof(case_tac a,cut_tac b1,simp) qed
      have b4:"substExp  e S=e" by(cut_tac b2 a1,auto)
      show "substExp  e (a # S) = e"
      by (simp add: b3 b4) 
    qed
   next
    show "?P2"
    proof
      assume b1:" set (varOfForm f) \<inter> set (map fst (a # S)) = {}"
      have b2:"set (varOfForm f) \<inter> set (map fst S) ={}" by(cut_tac b1,auto)
      have b3:" substForm  f (a # S) = substForm  f S" 
      proof(case_tac a,cut_tac b1,simp) qed
      have b4:"substForm  f S=f"
      by(cut_tac b2 a1,auto)
      show "substForm  f (a # S) = f"
      by (simp add: b3 b4) 
    qed
    qed
 qed
 
lemma noEffectPreExp [simp,intro!]:
  assumes a1:" v \<notin>set (varOfExp e)"
  shows " preExp1  e (Parallel (assign (v,e')#S))  = preExp1  e (Parallel S) "
  by (simp add: local.a1)
  
lemma noEffectPreExp1 [simp,intro!]:
  assumes a1:" set (varOfExp e) \<inter>  set (map fst ( map statement2Assigns S)) ={}"
  shows " preExp1  e (Parallel S)  =e "
  using assms noEffectSubstAllAux preExp1.simps(1) by presburger 
  
lemma noEffectPreCond [simp,intro!]:
  assumes a1:" v \<notin>set (varOfForm f)"
  shows " preCond1  f (Parallel (assign (v,e')#S))  = preCond1  f (Parallel S) "
  by (simp add: local.a1) 

lemma noEffectPreCond1 [simp,intro!]:
assumes a1: "(  (set (varOfForm f) \<inter> set (map fst S) ={} ) )"  
shows " substForm f S =  f"
using assms noEffectSubstAllAux by auto 
 

lemma auxOnCaseExpMaps[simp]:
"varOfExp (caseExp (map (\<lambda>i. (f i, e i)) (down LAST)))
=concat (map (\<lambda>i. ( (varOfForm (f i))@varOfExp ( e i)))  (down LAST))" 
proof(induct_tac LAST,auto)qed

lemma substByWrite[simp,intro!]:
  assumes a1:"(\<forall>j. Para mem j \<notin>set (varOfExp e'))"
shows "(substExp e'
       (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i)))) (down n))) =e'"
using a1 by(induct_tac n, auto)

lemma SucnIsNotInDownNAux: "\<forall>i. Suc n \<le> i \<longrightarrow> i \<notin> set (down n)"
proof(induct_tac n,auto)qed

lemma SucnIsNotInDownn: "Suc n \<notin> set (down n)"
by (simp add: SucnIsNotInDownNAux)

lemma OnIfPos1[simp,intro]:
  assumes a1:"tautlogy  (implyForm pre b) I" 
  shows "tautlogy  (implyForm pre (preCond1 f (If b S1 S2))) I = tautlogy  (implyForm pre (preCond1 f  S1 )) I " 
    by (cut_tac a1,auto)
    
lemma OnIfNeg1[simp,intro]:
  assumes a1:"tautlogy  (implyForm pre (neg b)) I" 
  shows "tautlogy  (implyForm pre (preCond1 f (If b S1 S2))) I = tautlogy  (implyForm pre (preCond1 f  S2 )) I "  
    by (cut_tac a1,auto) 

  
    
lemma preCondAndList[simp]:
shows "tautlogy (implyForm (preCond1 (andListForm FS) S) ( andListForm (map (\<lambda>f. preCond1 f S) FS))) I"
proof(induct_tac FS,simp,case_tac S,simp ,simp,rule allI)
  fix a list x21 x22 x23 s
  assume b1:" \<forall>s. (formEval I x21 s \<and> formEval I (preCond1 (andListForm list) x22) s \<longrightarrow>
            formEval I (andListForm (map (\<lambda>f. orForm (andForm x21 (preCond1 f x22)) (andForm (neg x21) (preCond1 f x23))) list)) s) \<and>
           (\<not> formEval I x21 s \<and> formEval I (preCond1 (andListForm list) x23) s \<longrightarrow>
            formEval I (andListForm (map (\<lambda>f. orForm (andForm x21 (preCond1 f x22)) (andForm (neg x21) (preCond1 f x23))) list)) s) " and 
         b2:"S = generalizeStatement.If x21 x22 x23 "
   show "(formEval I x21 s \<and> formEval I (preCond1 (andForm a (andListForm list)) x22) s \<longrightarrow>
        formEval I (preCond1 a x22) s \<and>
        formEval I (andListForm (map (\<lambda>f. orForm (andForm x21 (preCond1 f x22)) (andForm (neg x21) (preCond1 f x23))) list)) s) \<and>
       (\<not> formEval I x21 s \<and> formEval I (preCond1 (andForm a (andListForm list)) x23) s \<longrightarrow>
        formEval I (preCond1 a x23) s \<and>
        formEval I (andListForm (map (\<lambda>f. orForm (andForm x21 (preCond1 f x22)) (andForm (neg x21) (preCond1 f x23))) list)) s)"(is "?P \<and> ?Q")
    proof(rule conjI)    
      show "?P"
      proof
        assume c1:"formEval I x21 s \<and> formEval I (preCond1 (andForm a (andListForm list)) x22) s "
        show "formEval I (preCond1 a x22) s \<and> 
        formEval I (andListForm (map (\<lambda>f. orForm (andForm x21 (preCond1 f x22)) (andForm (neg x21) (preCond1 f x23))) list)) s"
        using b1 c1 lemmaOnPreForm by auto
      qed
      next
      show "?Q"
      proof
        assume c1:"\<not> formEval I x21 s \<and> formEval I (preCond1 (andForm a (andListForm list)) x23) s"
        show "formEval I (preCond1 a x23) s \<and> formEval I (andListForm (map (\<lambda>f. orForm (andForm x21 (preCond1 f x22)) (andForm (neg x21) (preCond1 f x23))) list)) s"
        using b1 c1 lemmaOnPreForm by auto
       qed 
       qed
qed

lemma preCondAndListConv[simp]:
shows "tautlogy (implyForm  ( andListForm (map (\<lambda>f. preCond1 f S) FS))  (preCond1 (andListForm FS) S)) I"
proof(induct_tac FS,case_tac S,simp,simp,rule allI)
  fix x21 x22 x23 s
  assume a1:"S = generalizeStatement.If x21 x22 x23"
  show "formEval I x21 s \<and> formEval I (preCond1 chaos x22) s \<or> \<not> formEval I x21 s \<and> formEval I (preCond1 chaos x23) s" thm lemmaOnPreForm
  by (simp add: lemmaOnPreForm)
  next
  fix a list
  assume a1:"tautlogy (implyForm (andListForm (map (\<lambda>f. preCond1 f S) list)) (preCond1 (andListForm list) S)) I"
  show "tautlogy (implyForm (andListForm (map (\<lambda>f. preCond1 f S) (a # list))) (preCond1 (andListForm (a # list)) S)) I"
  proof(simp,rule allI,rule impI)
    fix s
    assume b1:"formEval I (preCond1 a S) s \<and> formEval I (andListForm (map (\<lambda>f. preCond1 f S) list)) s "
    show "formEval I (preCond1 (andForm a (andListForm list)) S) s"
    proof(case_tac S)
      fix xs
      assume c1:"S=Parallel xs"
      show "formEval I (preCond1 (andForm a (andListForm list)) S) s"
      apply(cut_tac a1 b1 c1,simp) done
      next
      fix x21 x22 x23
      assume c1:"S=generalizeStatement.If x21 x22 x23"
      show "formEval I (preCond1 (andForm a (andListForm list)) S) s"
      apply(cut_tac a1 b1 c1,simp)
      using lemmaOnPreForm by auto
    qed
    qed
qed

end
