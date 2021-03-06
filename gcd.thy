theory gcd imports newparaGste1
begin

abbreviation x::"varType" where
"x \<equiv>  (Ident ''x'')"


abbreviation y::"varType" where
"y \<equiv>  (Ident ''y'')"

definition geRule::" rule" where [simp]:
"geRule\<equiv>
let g = uip ''>'' [IVar x, IVar y]  in
let s = parallel [(x, uif ''-'' [IVar x,IVar y])]  in
guard g s"

definition leRule::" rule" where [simp]:
"leRule\<equiv>
let g = uip ''<'' [IVar x, IVar y]  in
let s = parallel [(y, uif ''-'' [IVar y,IVar x])]  in
guard g s"

definition rules::" rule set" where [simp]:
"rules \<equiv> {
leRule, geRule
}"


subsection{*Definitions of initial states*}

consts x0::nat

consts y0::nat

definition initSpec0::" formula" where [simp]:
"initSpec0  \<equiv> andForm (eqn (IVar x) (Const (index x0))) (eqn (IVar y) (Const (index y0)))"

consts J::" interpretFunType"  
  

consts gcdSpec::"scalrValueType\<Rightarrow>scalrValueType\<Rightarrow>scalrValueType" 

axiomatization where axiomOnGe [simp,intro]:
" formEval J  (implyForm (uip ''>'' [e1, e2])   (eqn (uif ''gcd'' [e1, e2]) (uif ''gcd'' [(uif ''-'' [e1,e2]), e2]))) s"

axiomatization where axiomOnLe [simp,intro]:
" formEval J  (implyForm (uip ''<'' [e1, e2])   (eqn (uif ''gcd'' [e1, e2]) (uif ''gcd'' [  e1, (uif ''-'' [e2,e1])]))) s"

definition invariants::"formula set" where [simp]:
"invariants  \<equiv> {eqn (uif ''gcd'' [IVar x, IVar y]) (uif ''gcd'' [Const (index x0), Const (index y0)]) 
}"

lemma lemmaOnLe:
assumes a1: "(r=leRule)" and
a2: "f =eqn (uif ''gcd'' [IVar x, IVar y]) (uif ''gcd'' [Const (index x0), Const (index y0)])"
shows "invHoldForRule   J s f  r (invariants)"  (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
  have "?P3 s"
  proof(cut_tac a1 a2,unfold invHoldForRule3_def,rule_tac x="f" in exI,
      cut_tac axiomOnLe[where s="s" and ?e1.0="IVar x" and ?e2.0="IVar y"],simp,auto)
  qed
  then show "?thesis" by blast
qed

lemma lemmaOnGe:
assumes a1: "(r=geRule)" and
a2: "f =eqn (uif ''gcd'' [IVar x, IVar y]) (uif ''gcd'' [Const (index x0), Const (index y0)])"
shows "invHoldForRule   J s f  r (invariants)"  (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
  have "?P3 s"
  proof(cut_tac a1 a2,unfold invHoldForRule3_def,rule_tac x="f" in exI, 
      cut_tac axiomOnGe[where s="s" and ?e1.0="IVar x" and ?e2.0="IVar y"],simp,auto)
  qed
  then show "?thesis" by blast
qed


lemma invs_on_rules:
  assumes a1: "f \<in> invariants " and a2: "r \<in> rules "
  shows "invHoldForRule  J s f r (invariants )"
proof -

  have b1: "f =eqn (uif ''gcd'' [IVar x, IVar y]) (uif ''gcd'' [Const (index x0), Const (index y0)])"
    apply (cut_tac a1, auto) done
  have "r=geRule | r=leRule"
    using a2 by auto 
    moreover {
      assume c1: "r=geRule"
      have "invHoldForRule  J s f r (invariants )"
        using b1 c1 lemmaOnGe by blast
    }

  moreover {
      assume c1: "r=leRule"
      have "invHoldForRule  J s f r (invariants )"
        using b1 c1 lemmaOnLe by blast
    }
    ultimately show ?thesis by blast
qed


lemma iniImply_inv:
assumes a1:"f \<in> invariants " and a2: "formEval J (initSpec0) s"
shows "formEval J f s "
using a1 a2 by auto

lemma consistentGcd: 
  shows " consistent  J invariants {initSpec0} rules"
  using consistent_def iniImply_inv invs_on_rules by blast 


lemma gcdInv:
  assumes  a2:"s \<in> reachableSet J {initSpec0}  rules" 
  shows "\<forall> inv. inv \<in> invariants \<longrightarrow>formEval J inv s"  (is "?P s")
  using assms consistentGcd consistentLemma by blast
  
end