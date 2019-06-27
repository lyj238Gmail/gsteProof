theory newparaGsteSimp imports Main 
begin

section{*Variables and values*}

text{*
According to the aforementioned discussion in section ?, firstly we define the variables used in the protocols. 
There are two kinds of variables, global and parameterized (local) 
variables. In hardware implemetations of the protocols, 
the variables are implenteed as registers in global or local modules. *}

datatype varType=Ident  string | Para varType  nat |Field  varType   string 

datatype scalrValueType= index nat   | topVal | bottomVal

 

section{*Expressions and Formulas*}

datatype expType= IVar varType |
         Const scalrValueType |
         iteForm formula  expType  expType |
         uif string "expType list" |
         top |unKnown |
         readE  nat varType expType 


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

 
type_synonym assignType=  "varType \<times> nat\<times>  expType \<times> expType" 
(*a\<times>bound \<times>index \<times>content a[ie] = c where ie \<le> bound*)

definition paraNameOfAssign:: "assignType \<Rightarrow> varType" where
"paraNameOfAssign des \<equiv> fst des"

definition boundOfAssign:: "assignType \<Rightarrow> nat" where
"boundOfAssign des \<equiv> fst (snd des)"

definition leftIndexOfAssign:: "assignType \<Rightarrow> expType" where
"leftIndexOfAssign des \<equiv> fst (snd (snd des))"

definition rightOfAssign:: "assignType \<Rightarrow> expType" where
"rightOfAssign des \<equiv> snd (snd (snd des))"

text{*A statement is is just a lists of assignments, but these assignments
 are extecuted in parallel, \emph{not} in a sequential order*}

(*datatype statement=  assign assignType    *)

datatype statement=  parallel "assignType  list" 

text{*A parameterized statement is just a function from a parameter to a statement. 
For convenience, we also define the concatation of statements, and use it to define 
the $\mathsf{forall}$ statement.*}

type_synonym paraStatement= "nat \<Rightarrow> statement"


datatype rule =  guard formula  statement
text{*With the formalizatiion of formula and statement, 
it is natural to define a rule. A guard and
 statement of a rule are also defined for convenience. *}


primrec pre::"rule \<Rightarrow> formula" where
"pre (guard f a)=f"

primrec act::"rule \<Rightarrow>statement" where
"act  (guard f a)=a"



type_synonym paraRule=" nat \<Rightarrow> rule"
text{*A parameterized rule is just from a natural number to a rule.*}


   
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
"varOfExp   (readE bound  a e) =  map (\<lambda> i. Para a i) (upt 0 bound)" |

"varOfForm   (eqn e1 e2) = ( (varOfExp   e1 )  @   (varOfExp  e2))" |
"varOfForm   ( andForm f1 f2) =(  (varOfForm  f1 ) @  (varOfForm  f2 ))"|
"varOfForm   (neg f1 ) = (  (varOfForm   f1 ))"|
"varOfForm   (orForm f1 f2) =(  (varOfForm   f1 )   @   (varOfForm  f2 ))"|
"varOfForm   (implyForm f1 f2) = (  (varOfForm  f1 ) @ (varOfForm f2 ))"|
"varOfForm   (uip p es) = (concat (map varOfExp es))"|
"varOfForm   (chaos) =[]"
 

(*primrec  varOfSent::"statement \<Rightarrow> varType list" where
" varOfSent  (assign a)=[  (fst a)] " *)




section{*semantics of a protocol*}
text{*A  state of a protocol  is an instantaneous snapshot of its  behaviour given by an assignment of  values to variables of
the circuit. Therefore, we define:*}

type_synonym state= "varType \<Rightarrow> scalrValueType "


definition varsOfVar::" varType \<Rightarrow> varType set"  where  [simp]:
" varsOfVar x  = {x}" 


type_synonym scalrValueTypeListFun="scalrValueType list \<Rightarrow> scalrValueType"

type_synonym interpretFunType="string \<Rightarrow> scalrValueTypeListFun"

type_synonym scalrValueTypeListPred="scalrValueType list \<Rightarrow> bool"

type_synonym interpretPredType="string \<Rightarrow> scalrValueTypeListPred"

primrec scalar2Bool::"scalrValueType\<Rightarrow>bool" where
" scalar2Bool (index b) =( \<not>(b=0))" 

primrec getVal::"scalrValueType\<Rightarrow>nat" where
"getVal (index n) = n"

text{*A state transition from a state to another sate, which is caused by an execution of 
a statement, is  defined as follows:*}


primrec statement2Assigns::"statement \<Rightarrow> assignType list" where
"statement2Assigns (parallel  S)=S"



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
"expEval I (readE bound a e) s=  s (Para a (getVal (expEval I e s)))"|

evalExp: "formEval I (eqn e1 e2) s= ((expEval I e1 s) = (expEval I e2 s))" |
"formEval I  (uip p es)  s=    scalar2Bool ( (I p) (map (\<lambda> e. expEval  I e s) es)) " |
evalAnd: "formEval I ( andForm f1 f2) s=( (formEval I f1 s) \<and> (formEval I f2 s))"|
evalNeg: "formEval I (neg f1 ) s= ( \<not>(formEval I f1 s))"|
evalOr: "formEval I (orForm f1 f2) s=( (formEval I f1 s) \<or>  (formEval I f2 s))"|
evalImp:"formEval I (implyForm f1 f2) s= ( (formEval I f1 s) \<longrightarrow>  (formEval I f2 s))" |
"formEval I chaos s=True"

primrec getIndexOfExp::"expType \<Rightarrow> nat" where
"getIndexOfExp (Const i) =getVal i"


primrec valOf::" assignType list \<Rightarrow> varType =>nat\<Rightarrow>expType\<Rightarrow> expType"  where
"valOf   [] v bound indexE =IVar v
  " |
"valOf   (x#xs) v bound indexE= 
  (if ((paraNameOfAssign x) =v) \<and> (boundOfAssign x =0)   
  then (rightOfAssign x) 
  else (iteForm 
        (andForm (andForm (eqn (IVar v) (IVar (paraNameOfAssign x)))  (eqn (Const (index bound)) (Const (index (boundOfAssign x)))))
            (eqn  (leftIndexOfAssign x) indexE))
        (rightOfAssign x)
        ( valOf  xs v  bound indexE)))"
(*  else (if ((Para (paraNameOfAssign x) (getIndexOfExp (leftIndexOfAssign x))))= v 
        then (rightOfAssign x)
       else valOf  xs v ))"*)
(*a\<times>bound \<times>index \<times>content a[ie] = c where ie \<le> bound*)  


primrec transAux:: "assignType list \<Rightarrow>interpretFunType \<Rightarrow> state \<Rightarrow>bool\<times>state " where
"transAux [] I s= (True,s )" |
"transAux (asgn#asgns) I s=
  (let result=( transAux asgns I s) in
    if \<not>(fst result) then (False,s)
    else  
  (if (boundOfAssign asgn =0) then
    (True,  (snd result) ((paraNameOfAssign asgn):= expEval I ( rightOfAssign asgn) s) )
  else
    (let i=getVal (expEval I (leftIndexOfAssign asgn) s) in
    (if  i\<le> (boundOfAssign asgn)
    then (
           (True,(snd result)((Para (paraNameOfAssign asgn) i) := expEval I ( rightOfAssign asgn) s))
          )
    else  (False,s)
  )))) "

definition trans:: "statement \<Rightarrow> interpretFunType \<Rightarrow> state \<Rightarrow>bool \<times> state " where [simp]:
"trans S I s \<equiv> transAux ( statement2Assigns S) I s"



text{*The reachable sate set of a protocol, 
which is describled by a set of initiate formulas and a set of rules,
 can be formalized inductively as follows:*}


inductive_set reachableSet::" interpretFunType \<Rightarrow> formula set\<Rightarrow> rule set \<Rightarrow>state set" 
  for  I::"interpretFunType" and inis::"formula set"  and rules::"rule set"   where

initState:  "\<lbrakk>formEval  I ini s; ini \<in>  inis\<rbrakk>  \<Longrightarrow>(  s \<in>  ( reachableSet I inis rules))" |

oneStep:    " \<lbrakk>s \<in>  reachableSet I inis rules ;(fst (trans  (act r ) I s));
               r \<in>   rules ;formEval I (pre r ) s \<rbrakk> \<Longrightarrow>   (snd  (trans  (act r ) I s )) \<in>  reachableSet I inis rules"




section{*substitution, weakest precondition*}

primrec substExp :: "expType\<Rightarrow> assignType list \<Rightarrow>expType"  and 
substForm ::"formula \<Rightarrow> assignType list \<Rightarrow> formula" where 

substExpVar: "substExp  (IVar v') asgns=   (valOf  asgns v')  "| 

substExpConst: "substExp  (Const i)  asgns= Const i" |

substTop: "substExp top asgns=top" |

substUnkown: "substExp unKnown asgns=unKnown" |

substExpite: "substExp  (iteForm f e1 e2)  asgns= (iteForm (substForm f asgns) (substExp e1  asgns) (substExp e2  asgns))"|

substUif: "substExp (uif f es) asgns =( uif f (map (\<lambda>e. substExp e asgns) es))"| 


substReadE:"substExp   (readE bound a e) asgns=  readE bound a  (substExp e asgns)"|

"substForm (eqn l r)  asgns=(eqn (substExp l  asgns) (substExp r  asgns))"  |
"substForm ( andForm f1 f2)  asgns =   ( andForm (substForm f1  asgns)  (substForm f2  asgns))"|
"substForm (neg f1 )   asgns= (neg ( substForm f1  asgns ))"|
"substForm (orForm f1 f2)   asgns= ( orForm (substForm f1  asgns )  (substForm f2  asgns))"|
"substForm (implyForm f1 f2)   asgns= (implyForm (substForm f1 asgns)  (substForm f2  asgns))" |
"substForm (uip p es)   asgns= ( uip p (map (\<lambda>e. substExp e asgns) es))" |
"substForm  chaos   asgns=chaos"





primrec  preCond1 ::" formula \<Rightarrow> statement  \<Rightarrow>formula" where
"preCond1 f ( parallel  S)  = substForm f S " 


primrec  preExp1 ::" expType \<Rightarrow>  statement  \<Rightarrow>expType" where [simp]:
"preExp1 e  (parallel  S)  = substExp e S"


lemma lemmaOnValOf:  shows "expEval I (preExp1 (IVar v) nf) s = trans nf I s v" 
  (is "?LHS1 nf =?RHS1 nf ")
proof(induct_tac nf)
  fix x
  let ?nf="parallel x"
  show "?LHS1 ?nf=?RHS1 ?nf"
  proof(auto)
  show "expEval I (valOf x v) s = transAux x I  s v"
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

qed

lemma itePreExp1:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (trans  nf I s)  
   \<longrightarrow> expEval I (preExp1 x2 nf) s = expEval I x2 (trans  nf I s)
   \<longrightarrow>  expEval I (preExp1 x3 nf) s = expEval I x3 (trans  nf I s)
   \<longrightarrow>   expEval I (preExp1 (iteForm x1 x2 x3) nf) s = expEval I (iteForm x1 x2 x3) (trans  nf I s)"
   (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?p3 nf\<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf \<longrightarrow>?p3 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto

qed

lemma eqPre:
  "expEval I (preExp1 x1 nf) s = expEval I x1 (trans nf I s)\<longrightarrow>
   expEval I (preExp1 x2 nf) s = expEval I x2 (trans nf I s)\<longrightarrow>
   formEval I (preCond1 (eqn x1 x2) nf) s = formEval I (eqn x1 x2) (trans nf I s)"
   (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto

qed  

lemma auxOnufiPre: "(\<forall>x2a. x2a \<in> set es \<longrightarrow> expEval I (preExp1 x2a (parallel S)) s = expEval I x2a (trans (parallel S) I s)) \<longrightarrow>
 (map ((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e S)) es) =
      (map (\<lambda>e. expEval I e (transAux S I s)) es)" (is "?P es")
proof(induct_tac es)
  let ?nf="parallel S"
  show "?P []" by auto
  next 
  fix x xs
  assume b1:"?P xs"
  show "?P (x#xs)" (is "?P1 (x#xs) \<longrightarrow> ?P2 (x#xs)")
  proof 
  assume c1:"?P1 (x#xs)"
  have b2:"?P1 xs" by (cut_tac c1,auto )
  then have b3:"?P2 xs" by(cut_tac b1,auto)
  
    
   have b5:"((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e S)) x =
  (\<lambda>e. expEval I e (transAux S I s)) x" 
    by (cut_tac c1,simp) 
  
  show "?P2 (x#xs)" (is "?LHS (x#xs) = ?RHS (x#xs)")
  by(cut_tac b5 b3, auto)
  qed
qed

lemma uifPre:  

" (\<forall>x2a. x2a \<in> set es \<longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (trans nf I s)) \<longrightarrow>
             expEval I (preExp1 (uif f es) nf) s = expEval I (uif f es) (trans nf I s)   "   
           (  is "?p1 nf\<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   
   show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   proof 
   assume a1:"?p1 ?nf"
   have b1:"(map ((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e S)) es) =
      (map (\<lambda>e. expEval I e (transAux S I s)) es)"
      using a1 by auto
   
      
   then show "?LHS ?nf=?RHS ?nf" apply simp
   apply( simp add:b1)
   done
   qed

qed  

lemma uipPre:  

" (\<forall>x2a. x2a \<in> set es \<longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (trans nf I s)) \<longrightarrow>
             formEval I (preCond1 (uip pn es) nf) s =formEval I (uip pn es) (trans nf I s)   "   
           (  is "?p1 nf\<longrightarrow>?LHS nf=?RHS nf")
 proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   
   show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   proof 
   assume a1:"?p1 ?nf"
   have b1:"(map ((\<lambda>e. expEval I e s) \<circ> (\<lambda>e. substExp e S)) es) =
      (map (\<lambda>e. expEval I e (transAux S I s)) es)"
      using a1 by auto
   then show "?LHS ?nf=?RHS ?nf" apply simp
   apply( simp add:b1)
   done
   qed

qed  

lemma andPre:       
  "formEval I (preCond1 x1 nf) s = formEval I x1 (trans nf I s) \<longrightarrow>
   formEval I (preCond1 x2 nf) s = formEval I x2 (trans nf I s) \<longrightarrow>
   formEval I (preCond1 (andForm x1 x2) nf) s = formEval I (andForm x1 x2) (trans nf I s)"    
    (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto

qed        

lemma orPre:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (trans nf I s) \<longrightarrow>
   formEval I (preCond1 x2 nf) s = formEval I x2 (trans nf I s) \<longrightarrow>
   formEval I (preCond1 (orForm x1 x2) nf) s = formEval I (orForm x1 x2) (trans nf I s)"    
    (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto

qed      

lemma implyPre:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (trans nf I s) \<longrightarrow>
   formEval I (preCond1 x2 nf) s = formEval I x2 (trans nf I s) \<longrightarrow>
   formEval I (preCond1 (implyForm x1 x2) nf) s = formEval I (implyForm x1 x2) (trans nf I s)"    
    (is "?p1 nf\<longrightarrow>?p2 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   show "?p1 ?nf \<longrightarrow>?p2 ?nf  \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto

qed    

lemma notPre:
  "formEval I (preCond1 x1 nf) s = formEval I x1 (trans nf I s) \<longrightarrow>
   formEval I (preCond1 (neg x1 ) nf) s = formEval I (neg x1 ) (trans nf I s)"    
    (is "?p1 nf \<longrightarrow>?LHS nf=?RHS nf")
proof(induct_tac nf)
   fix S
   let ?nf="parallel S"
   show "?p1 ?nf \<longrightarrow>?LHS ?nf=?RHS ?nf"
   by auto

qed       

lemma lemmaOnPre:
  shows "(expEval I (preExp1 e nf) s =   expEval I  e (trans nf I s)) \<and>
   (formEval I (preCond1 f nf) s = formEval I f (trans nf I s))"
   (is "((  ?LHS e =?RHS e )\<and> ( ?LHS1 f =?RHS1 f ))")      
proof(induct_tac e and f)
  fix v
  let ?e="(IVar v)"
  show  "  ?LHS ?e =?RHS ?e "
  apply(simp)
  by (simp add: lemmaOnValOf)
 
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
  assume a1:"(\<And>x2a. x2a \<in> set es \<Longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (trans nf I s))"
   show "?LHS ?e =?RHS ?e " (is "?LHS1 nf=?RHS1 nf")
   by (simp add: a1 uifPre)
next
  fix pn es
  let ?f="uip pn es"
  assume a1:"(\<And>x2a. x2a \<in> set es \<Longrightarrow> expEval I (preExp1 x2a nf) s = expEval I x2a (trans nf I s))"
   show "?LHS1 ?f =?RHS1 ?f "  
   by (simp add: a1 uipPre)
qed



lemma lemmaOnPreExp:  
shows "expEval I (preExp1 e nf) s =   expEval I e (trans nf I s) "
  by (simp add: lemmaOnPre)

lemma lemmaOnPreForm:  
shows "formEval I (preCond1 f nf) s = formEval I f (trans nf I s)"
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


section{*causal relations and consistency lemma*}
text{*A novel feature of our work lies in that three kinds of causal
relations are exploited, which are essentially special cases of the
general induction rule.  Consider a rule $r$, a formula $f$, and a formula set $fs$, three
 kinds of causal relations are defined as follows:*}

definition invHoldForRule1::"interpretFunType\<Rightarrow> state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow> bool" where [simp]:
"invHoldForRule1 I s f  r \<equiv>  
(formEval I (pre r) s \<longrightarrow>  formEval I (preCond1 f  (act r)) s )"
text{* $\mathsf{invHoldRule}_1(s,f, r)$ means that after rule $r$ is executed, $f$ becomes true immediately;*}

 definition invHoldForRule2::"interpretFunType\<Rightarrow> state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow> bool" where [simp]:
"invHoldForRule2 I s f  r \<equiv>  
(formEval I (preCond1 f  (act r)) s  =  formEval I f s)"
text{*$\mathsf{invHoldRule}_2(s,f, r)$ states that $\mathsf{preCond}(S,f)$ is equivalent to $f$, 
which intuitively means that none of state variables in $f$ is changed, and the execution of 
statement $S$ does not affect the evaluation of $f$;*}

definition  invHoldForRule3::"interpretFunType\<Rightarrow>state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow>formula set\<Rightarrow> bool"  where [simp]:
"invHoldForRule3 I s f r fs  \<equiv>  
(\<exists>f'. f' \<in> fs \<and>  (formEval  I (andForm (pre r)  f') s\<longrightarrow> formEval I (preCond1 f  (act r))  s))"  
text{*$\mathsf{invHoldRule}_3(s,f, r,fs)$ states that there exists another invariant $f' \in fs$ such that
  the conjunction of the guard of $r$ and $f'$ implies the precondition  $\mathsf{preCond}(S,f)$.*}

abbreviation invHoldForRule::"interpretFunType\<Rightarrow>state \<Rightarrow>formula \<Rightarrow> rule \<Rightarrow> (formula set) \<Rightarrow> bool" where
  "invHoldForRule I s inv0 r invs \<equiv>
    invHoldForRule1 I s inv0 r \<or>  invHoldForRule2 I s inv0 r \<or>   invHoldForRule3 I s inv0 r invs "


text{*The relation $\mathsf{invHoldRule}(s, f,r,fs)$ defines a causality relation
between $f$, $r$, and $fs$, which guarantees that if each formula in $fs$ holds
before the execution of rule $r$, then $f$ holds after the execution of rule $r$.
We can also view $\mathsf{invHoldRule}(s, f, r, fs)$ as a
special kind of inductive tactics, which can be applied to prove
each formula in $fs$ holds at each inductive protocol rule cases. 
Note that the three kinds of inductive tactics can be done by a theorem prover, 
which is the cornerstone of our work.

With the $\mathsf{invHoldRule}$ relation, we define a consistency relation 
$\mathsf{consistent}( invs,inis, rs)$ between a protocol $(inis,rs)$ and a
 set of invariants $invs=\{inv_1,\ldots, inv_n\}$. *}


definition consistent::"interpretFunType\<Rightarrow>formula set \<Rightarrow> formula set \<Rightarrow> rule set \<Rightarrow>bool"  where [simp]:
"consistent I invs inis rs \<equiv>
(\<forall>inv ini s. (inv \<in> invs \<longrightarrow> ini\<in> inis\<longrightarrow> formEval I ini s \<longrightarrow> formEval I inv s)) \<and>
 (\<forall> inv r s.  (inv \<in>invs  \<longrightarrow> r \<in> rs \<longrightarrow> invHoldForRule I s inv r invs  ))"   


definition  invHoldForRule4::"interpretFunType\<Rightarrow>state \<Rightarrow> formula \<Rightarrow> rule \<Rightarrow>formula set\<Rightarrow> bool"  where [simp]:
"invHoldForRule4 I s f r fs  \<equiv>  
(\<exists>fs'. fs' \<subseteq> fs \<and>  ((\<forall> f'. f'\<in>(fs' \<union> {pre r}) \<longrightarrow>formEval  I   f' s)\<longrightarrow> formEval I (preCond1 f  (act r))  s))"  


abbreviation invHoldForRule'::"interpretFunType\<Rightarrow>state \<Rightarrow>formula \<Rightarrow> rule \<Rightarrow> (formula set) \<Rightarrow> bool" where
  "invHoldForRule' I s inv0 r invs \<equiv>
    invHoldForRule1 I s inv0 r \<or>  invHoldForRule2 I s inv0 r \<or>   invHoldForRule4 I s inv0 r invs "


text{*$\mathsf{invHoldRule}_3(s,f, r,fs)$ states that there exists another invariant $f' \in fs$ such that
  the conjunction of the guard of $r$ and $f'$ implies the precondition  $\mathsf{preCond}(S,f)$.*}


lemma consistentLemma:
  assumes a1:"consistent I invs inis rs" and a2:"s \<in> reachableSet I inis rs" 
  shows "\<forall> inv. inv \<in> invs \<longrightarrow>formEval I inv s"  (is "?P s")
  using a2
  proof induct
    case (initState ini s)
    show "?P s"
      apply(cut_tac a1, unfold consistent_def)
      by (metis (lifting) initState(1) initState(2))
  next
    case (oneStep s r)
    show "?P  (trans  (act r) I s)"    
    proof (rule allI, rule impI)
      fix inv
      assume b1:"inv \<in> invs"
      have b2:" invHoldForRule3 I s inv r  invs \<or> invHoldForRule2 I s inv r   \<or> invHoldForRule1 I s inv r  "
        apply(cut_tac a1, unfold consistent_def)
        by (metis b1 oneStep(3))
        
     moreover
      { assume c1:"invHoldForRule3 I s inv r invs"
        
        let ?pref="preCond1 inv (act r)"
          have b3:"  ( (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval I f'  s) \<longrightarrow>formEval I (pre r)  s\<longrightarrow> formEval I  ?pref s)  "  (is " ?P fs ")
           apply (cut_tac c1, unfold invHoldForRule3_def,auto)
          done

        then have b3':"?P fs  "
          by blast

        have b4:" (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval I f'  s)"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:"formEval I (pre r) s"
          by (metis (lifting) oneStep(4))

        have b6:"formEval I ?pref s"
         by(cut_tac b4 b5 b3', auto)

        have "formEval I inv (trans (act r) I s)"
          using b6 lemmaOnPre by blast
      }
     
     moreover
      {assume b1':"invHoldForRule2 I s inv r "
        have b2:"formEval I inv s"
        by (metis b1 oneStep.hyps(2))
        
        let ?pref="preCond1 inv (act r)"
        have b3:" (  formEval I ?pref s  =  formEval I inv s)"
        by(cut_tac b1',unfold  invHoldForRule2_def,simp)
        
        with b2 have b4:"formEval I ?pref s"
          by auto
          
        have "formEval I inv (trans (act r) I s)"
          using b2 b3 lemmaOnPreForm by auto
         
      }
      moreover
      {assume b1':"invHoldForRule1 I s inv r "
         
         have b5:"formEval I (pre r) s"
          by (metis (lifting) oneStep(4))
        
         have "formEval I inv (trans (act r) I s)"
           apply(subgoal_tac "formEval I (preCond1 inv (act r) ) s")
           apply (simp add: lemmaOnPre)
           apply(cut_tac b1' b5)
           by(unfold invHoldForRule1_def,auto)
       
       }
       ultimately show "formEval I inv (trans (act r) I s)"
         by blast
     qed
 qed  

definition consistent'::"interpretFunType\<Rightarrow>formula set \<Rightarrow> formula set \<Rightarrow> rule set \<Rightarrow>bool"  where [simp]:
"consistent' I invs inis rs \<equiv>
(\<forall>inv ini s. (inv \<in> invs \<longrightarrow> ini\<in> inis\<longrightarrow> formEval I ini s \<longrightarrow> formEval I inv s)) \<and>
 (\<forall> inv r s.  (inv \<in>invs  \<longrightarrow> r \<in> rs \<longrightarrow> invHoldForRule' I s inv r invs  ))"   
  

lemma consistentLemma':
  assumes a1:"consistent' I invs inis rs" and a2:"s \<in> reachableSet I inis rs" 
  shows "\<forall> inv. inv \<in> invs \<longrightarrow>formEval I inv s"  (is "?P s")
  using a2
  proof induct
    case (initState ini s)
    show "?P s"
      apply(cut_tac a1, unfold consistent'_def)
      by (metis (lifting) initState(1) initState(2))
  next
    case (oneStep s r)
    show "?P  (trans  (act r) I s)"    
    proof (rule allI, rule impI)
      fix inv
      assume b1:"inv \<in> invs"
      have b2:" invHoldForRule4 I s inv r  invs \<or> invHoldForRule2 I s inv r   \<or> invHoldForRule1 I s inv r  "
        apply(cut_tac a1, unfold consistent'_def)
        by (metis b1 oneStep(3))
        
     moreover
      { assume c1:"invHoldForRule4 I s inv r invs"
        
        let ?pref="preCond1 inv (act r)"
          have b3:"  ( (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval I f'  s) \<longrightarrow>formEval I (pre r)  s\<longrightarrow> formEval I  ?pref s)  "  (is " ?P fs ")
           apply (cut_tac c1, unfold invHoldForRule4_def,auto)
          done

        then have b3':"?P fs  "
          by blast

        have b4:" (\<forall> f'.  f' \<in>  invs\<longrightarrow>formEval I f'  s)"
          apply(cut_tac b3' )
          by (metis (no_types) oneStep(2))

        have b5:"formEval I (pre r) s"
          by (metis (lifting) oneStep(4))

        have b6:"formEval I ?pref s"
         by(cut_tac b4 b5 b3', auto)

        have "formEval I inv (trans (act r) I s)"
          using b6 lemmaOnPre by blast
      }
     
     moreover
      {assume b1':"invHoldForRule2 I s inv r "
        have b2:"formEval I inv s"
        by (metis b1 oneStep.hyps(2))
        
        let ?pref="preCond1 inv (act r)"
        have b3:" (  formEval I ?pref s  =  formEval I inv s)"
        by(cut_tac b1',unfold  invHoldForRule2_def,simp)
        
        with b2 have b4:"formEval I ?pref s"
          by auto
          
        have "formEval I inv (trans (act r) I s)"
          using b2 b3 lemmaOnPreForm by auto
         
      }
      moreover
      {assume b1':"invHoldForRule1 I s inv r "
         
         have b5:"formEval I (pre r) s"
          by (metis (lifting) oneStep(4))
        
         have "formEval I inv (trans (act r) I s)"
           apply(subgoal_tac "formEval I (preCond1 inv (act r) ) s")
           apply (simp add: lemmaOnPre)
           apply(cut_tac b1' b5)
           by(unfold invHoldForRule1_def,auto)
       
       }
       ultimately show "formEval I inv (trans (act r) I s)"
         by blast
     qed
 qed  

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

lemma valOfLemma4Aux :"v \<notin> set (map fst   ( statement2Assigns (parallel S))) \<longrightarrow>
( valOf ( statement2Assigns  (parallel ( S@ S'))) v) =    ( valOf ( statement2Assigns (parallel S')) v)"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma4 [simp,intro]:"v \<notin> set (map fst   ( statement2Assigns (parallel S))) \<Longrightarrow>
( valOf ( statement2Assigns  (parallel ( S@ S'))) v) =    ( valOf ( statement2Assigns (parallel S')) v)"
by (metis valOfLemma4Aux)

lemma valOfLemma5Aux :"v \<notin> set (map fst  As') \<longrightarrow>
( valOf (As'@ As) v) =    ( valOf As) v"
    proof(induct_tac As',auto)qed

lemma valOfLemma5 :"v \<notin> set (map fst  As') \<Longrightarrow>
( valOf (As'@ As) v) =    ( valOf As) v"
   by (metis valOfLemma5Aux)  
   
(*lemma mapFstAssignsAux:"(\<forall> i.  v' \<noteq> Para v i) \<longrightarrow> v' \<notin> set (map fst ( map (statement2Assigns o 
                      (\<lambda>i. assign (Para v i,  e i))) L )) "
  apply(induct_tac L,auto) done              
  
lemma mapFstAssigns [simp,intro]:"(\<forall> i.  v' \<noteq> Para v i) \<Longrightarrow> v' \<notin> set (map fst ( map (statement2Assigns o 
                      (\<lambda>i. assign (Para v i,  e i))) L )) "
  apply(metis mapFstAssignsAux) done
*)  
lemma valOfLemma6Aux :"v \<notin> set (map fst   S) \<longrightarrow>
( valOf  ( S@ S') v) =    ( valOf   S') v"
    proof(induct_tac S,auto)qed
    
    

lemma valOfLemma6 [simp,intro!]:"v \<notin> set (map fst   S) \<Longrightarrow>
( valOf  ( S@ S') v) =    ( valOf   S') v"
by (metis valOfLemma6Aux)


(*
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
*)
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

(*lemma valOfLemma10:"
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
     *)
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
  shows " preExp1  e (parallel ( (v,e')#S))  = preExp1  e (parallel S) "
  by (simp add: local.a1)
  
lemma noEffectPreExp1 [simp,intro!]:
  assumes a1:" set (varOfExp e) \<inter>  set (map fst (  statement2Assigns (parallel S))) ={}"
  shows " preExp1  e (parallel S)  =e "
  using assms noEffectSubstAllAux by auto
  
lemma noEffectPreCond [simp,intro!]:
  assumes a1:" v \<notin>set (varOfForm f)"
  shows " preCond1  f (parallel ( (v,e')#S))  = preCond1  f (parallel S) "
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

(*lemma OnIfPos1[simp,intro]:
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
*)
end
