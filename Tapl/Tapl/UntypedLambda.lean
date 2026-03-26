import Mathlib.Tactic

namespace UntypedLambda
  inductive Term: Type where 
  | Var: String → Term
  | Lambda: String → Term → Term 
  | App: Term → Term → Term

  def free_vars: Term → List String
  | Term.Var v => [v]
  | Term.Lambda v t => (free_vars t).filter (λ var => var ≠ v)
  | Term.App t₁ t₂ => free_vars t₁ ++ free_vars t₂ 

  def subst (v:String) (t:Term): Term → Term 
  | Term.Var v₂ => if v == v₂ then t else Term.Var v₂ 
  | Term.Lambda v₂ t₂ => if v ≠ v₂ ∧ v₂ ∉ free_vars t then 
    Term.Lambda v₂ (subst v t t₂) else
    Term.Lambda v₂ t₂ 
  | Term.App t₁ t₂ => Term.App (subst v t t₁) (subst v t t₂)

  inductive Value: Term → Prop where
  | valLambda (v:String) (t:Term): Value (Term.Lambda v t)

  abbrev Closed (t:Term): Prop := free_vars t = []

  lemma free_subst: ∀ (t₁ t₂:Term) (v:String), v ∉ free_vars t₁ → subst v t₂ t₁ = t₁ := by 
  intro t₁ t₂ v h_var
  induction t₁
  case Var v₂ => 
    simp [subst]
    intro h_eq 
    simp [free_vars] at h_var 
    contradiction
  case Lambda v₂ t₃ h_ind =>
    simp [subst]
    intro h_neq h_notin
    apply h_ind 
    simp [free_vars] at h_var 
    by_contra
    apply h_var at this
    contradiction
  case App t₃ t₄ h_ind₃ h_ind₄ =>
    simp [subst]
    simp [free_vars] at h_var 
    rcases h_var with ⟨h_varl,h_varr⟩
    constructor
    case left => apply h_ind₃; exact h_varl
    case right => apply h_ind₄; exact h_varr 

  lemma subst_closed: ∀ (t₁ t₂:Term) (v:String), Closed t₁ → subst v t₂ t₁ = t₁ := by 
  intro t₁ t₂ v h_closed
  apply free_subst
  unfold Closed at h_closed 
  rw [h_closed]
  simp


  inductive Eval: Term → Term → Prop where 
  | evalBeta (v:String) (t₁ t₂:Term): 
    Value t₁ → Eval (Term.App (Term.Lambda v t₂) t₁) (subst v t₁ t₂)
  | evalAppLeft (t₁ t₂ t₃: Term) :
    Eval t₁ t₃ →
    Eval (Term.App t₁ t₂) (Term.App t₃ t₂)
  | evalAppRight (t₁ t₂ t₃: Term):
    Value t₁ → Eval t₂ t₃ → 
    Eval (Term.App t₁ t₂) (Term.App t₁ t₃)

  inductive EvalStar: Term → Term → Prop where 
  | evalRefl (t:Term): EvalStar t t
  | evalTrans (t₁ t₂ t₃: Term): Eval t₁ t₂ → EvalStar t₂ t₃ → EvalStar t₁ t₃

  def church_true: Term := Term.Lambda "t" (Term.Lambda "f" (Term.Var "t"))
  def church_false: Term := Term.Lambda "t" (Term.Lambda "f" (Term.Var "f"))
  def church_if: Term := Term.Lambda "l" (Term.Lambda "m" (Term.Lambda "n" 
    (Term.App (Term.App (Term.Var "l")  (Term.Var "m")) (Term.Var "n"))))

  lemma closed_tru: Closed church_true := by 
    simp [Closed,church_true,free_vars]

  lemma closed_fls: Closed church_false := by 
    simp [Closed,church_false,free_vars]

  lemma app_tru: ∀ (t₁ t₂:Term) (_: Value t₁) (_: Value t₂) 
  (_:Closed t₁) (_:Closed t₂),
  EvalStar (Term.App (Term.App church_true t₁) t₂) t₁ := by 
  intro t₁ t₂ h_val₁ h_val₂ h_closed₁ h_closed₂
  apply EvalStar.evalTrans
  apply Eval.evalAppLeft 
  apply Eval.evalBeta
  apply h_val₁ 
  simp [subst]
  unfold Closed at h_closed₁ 
  rw [h_closed₁] 
  simp
  apply EvalStar.evalTrans
  apply Eval.evalBeta
  apply h_val₂
  have h: (subst "f" t₂ t₁) = t₁ := by 
    apply subst_closed
    unfold Closed 
    exact h_closed₁ 
  rw [h]
  apply EvalStar.evalRefl

  lemma app_fls: ∀(t₁ t₂:Term) (_:Value t₁) (_:Value t₂) 
  (_:Closed t₁) (_:Closed t₂),
  EvalStar (Term.App (Term.App church_false t₁) t₂) t₂ := by 
  intro t₁ t₂ h_val₁ h_val₂ h_closed₁ h_closed₂
  apply EvalStar.evalTrans
  apply Eval.evalAppLeft
  apply Eval.evalBeta
  apply h_val₁ 
  simp [subst]
  apply EvalStar.evalTrans
  apply Eval.evalBeta
  apply h_val₂ 
  simp [subst]
  apply EvalStar.evalRefl



  lemma ite_tru: ∀ (t₁ t₂:Term) (_:Value t₁) (_: Value t₂) 
  (_:Closed t₁) (_:Closed t₂),
  EvalStar (Term.App (Term.App (Term.App church_if church_true) t₁) t₂) t₁ := by 
  intro t₁ t₂ h_val₁ h_val₂ h_closed₁ h_closed₂
  apply EvalStar.evalTrans
  apply Eval.evalAppLeft 
  apply Eval.evalAppLeft
  apply Eval.evalBeta
  constructor
  simp [subst]
  have h:= closed_tru
  unfold Closed at h 
  rw [h]
  simp
  apply EvalStar.evalTrans
  apply Eval.evalAppLeft 
  apply Eval.evalBeta
  apply h_val₁ 
  simp [subst]
  unfold Closed at h_closed₁
  rw [h_closed₁ ]
  simp
  have h₂: subst "m" t₁ church_true = church_true := by 
    simp [church_true,subst]
  rw [h₂]
  apply EvalStar.evalTrans
  apply Eval.evalBeta
  apply h_val₂ 
  simp [subst]
  have h₃: subst "n" t₂ church_true = church_true := by 
    simp [church_true,subst]
  rw [h₃]
  have h₄ : subst "n" t₂ t₁ = t₁ := by 
    apply subst_closed
    unfold Closed 
    exact h_closed₁ 
  rw [h₄]
  apply app_tru
  apply h_val₁ 
  apply h_val₂ 
  unfold Closed 
  apply h_closed₁ 
  apply h_closed₂ 

  def church_and: Term := Term.Lambda "b" (Term.Lambda "c" 
    (Term.App (Term.App (Term.Var "b") (Term.Var "c")) church_false))

  lemma and_tru_tru: 
    EvalStar 
    (Term.App (Term.App church_and church_true) church_true)
    church_true := by 
    unfold church_and
    apply EvalStar.evalTrans
    apply Eval.evalAppLeft 
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h:= closed_tru
    unfold Closed at h
    rw [h]
    simp
    have h₂: subst "b" church_true church_false = church_false := by 
      simp [church_false,subst]
    rw [h₂]
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h₃: subst "c" church_true church_true = church_true := by 
      simp [church_true,subst]
    rw [h₃]
    have h₄: subst "c" church_true church_false = church_false := by 
      simp [church_false,subst]
    rw [h₄]
    apply app_tru
    constructor
    constructor
    unfold Closed 
    apply h 
    apply closed_fls

  lemma and_tru_fls: EvalStar 
    (Term.App (Term.App church_and church_true) church_false) church_false := by 
    unfold church_and
    apply EvalStar.evalTrans
    apply Eval.evalAppLeft 
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h:= closed_tru
    unfold Closed at h 
    rw [h]
    simp 
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h₂: subst "c" church_false church_true = church_true := by
      simp [church_true,subst]
    rw [h₂]
    have h₃: subst "b" church_true church_false = church_false := by 
      simp [church_false,subst]
    rw [h₃]
    have h₄: subst "c" church_false church_false = church_false := by 
      simp [church_false,subst]
    rw [h₄]
    apply app_tru
    constructor
    constructor
    apply closed_fls
    apply closed_fls

  def church_or: Term := Term.Lambda "b" (Term.Lambda "c" 
    (Term.App (Term.App (Term.Var "b") church_true) (Term.Var "c")))

  lemma or_fls_fls: EvalStar 
    (Term.App (Term.App church_or church_false) church_false)
    church_false := by 
    unfold church_or
    apply EvalStar.evalTrans
    apply Eval.evalAppLeft 
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h:=closed_fls
    unfold Closed at h 
    rw [h]
    simp 
    have h₂: subst "b" church_false church_true = church_true := by 
      simp [church_true,subst]
    rw [h₂]
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h₃: subst "c" church_false church_false = church_false := by 
      simp [church_false,subst]
    rw [h₃]
    have h₄: subst "c" church_false church_true = church_true := by 
      simp [church_true,subst]
    rw [h₄]
    apply app_fls
    constructor
    constructor
    apply closed_tru
    apply closed_fls

  lemma or_tru_fls: EvalStar 
    (Term.App (Term.App church_or church_true) church_false) 
    church_true := by 
    unfold church_or 
    apply EvalStar.evalTrans
    apply Eval.evalAppLeft
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h:= closed_tru
    unfold Closed at h
    rw [h]
    simp
    have h₂ : subst "b" church_true church_true = church_true := by 
      simp [church_true,subst]
    rw [h₂]
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h₃: subst "c" church_false church_true = church_true := by 
      simp [church_true,subst]
    rw [h₃] 
    apply app_tru
    constructor
    constructor
    apply closed_fls
    apply closed_fls
    
  def church_not: Term := Term.Lambda "b" 
    (Term.App (Term.App (Term.Var "b") church_false) church_true)
  
  lemma not_true: EvalStar (Term.App church_not church_true) church_false := by 
    unfold church_not
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h: subst "b" church_true church_false = church_false := by 
      simp [church_false,subst]
    rw [h]
    have h₂: subst "b" church_true church_true = church_true := by 
      simp [church_true,subst]
    rw [h₂]
    apply app_tru
    constructor
    constructor
    apply closed_fls
    apply closed_tru
  
  lemma not_false: EvalStar (Term.App church_not church_false) church_true := by 
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    simp [subst]
    have h: subst "b" church_false church_false = church_false := by 
      simp [church_false,subst]
    rw [h]
    have h₂: subst "b" church_false church_true = church_true := by 
      simp [church_true,subst]
    rw [h₂]
    apply app_fls
    constructor
    constructor
    apply closed_fls
    apply closed_tru

  def church_pair: Term := Term.Lambda "f" (Term.Lambda "s" (Term.Lambda "b" 
    (Term.App (Term.App (Term.Var "b") (Term.Var "f")) (Term.Var "s"))))

  def church_fst: Term := Term.Lambda "p" (Term.App (Term.Var "p") church_true)

  def church_snd: Term := Term.Lambda "p" (Term.App (Term.Var "p") church_false)

  lemma pair_fst: ∀ (t₁ t₂:Term) (_:Value t₁) (_:Value t₂) 
  (_:Closed t₁) (_:Closed t₂),
  EvalStar (Term.App church_fst (Term.App (Term.App church_pair t₁) t₂)) t₁ := by 
  intro t₁ t₂ h_val₁ h_val₂ h_closed₁ h_closed₂
  apply EvalStar.evalTrans
  apply Eval.evalAppRight
  constructor
  apply Eval.evalAppLeft 
  apply Eval.evalBeta
  apply h_val₁
  unfold Closed at h_closed₁
  simp [subst,h_closed₁]
  apply EvalStar.evalTrans
  apply Eval.evalAppRight
  constructor
  apply Eval.evalBeta
  apply h_val₂
  unfold Closed at h_closed₂
  simp [subst,h_closed₂]
  have h:subst "s" t₂ t₁ = t₁ := by 
    apply subst_closed
    unfold Closed 
    exact h_closed₁
  rw [h]
  apply EvalStar.evalTrans
  apply Eval.evalBeta
  constructor
  simp [subst]
  have h₂: ∀(t:Term), subst "p" t church_true = church_true := by 
    intro t 
    apply subst_closed 
    apply closed_tru
  rw [h₂]
  apply EvalStar.evalTrans
  apply Eval.evalBeta
  constructor
  simp [subst]
  have h₃: subst "b" church_true t₁ = t₁ := by 
    apply subst_closed 
    unfold Closed 
    exact h_closed₁ 
  rw [h₃]
  have h₄: subst "b" church_true t₂ = t₂ := by 
    apply subst_closed
    unfold Closed
    exact h_closed₂
  rw [h₄]
  apply app_tru
  apply h_val₁ 
  apply h_val₂ 
  unfold Closed 
  apply h_closed₁ 
  unfold Closed 
  apply h_closed₂

  lemma pair_snd: ∀ (t₁ t₂:Term) (_:Value t₁) (_:Value t₂) 
  (_:Closed t₁) (_:Closed t₂),
  EvalStar (Term.App church_snd (Term.App (Term.App church_pair t₁) t₂)) t₂ := by 
  intro t₁ t₂ h_val₁ h_val₂ h_closed₁ h_closed₂
  apply EvalStar.evalTrans
  apply Eval.evalAppRight
  constructor
  apply Eval.evalAppLeft 
  apply Eval.evalBeta
  apply h_val₁
  unfold Closed at h_closed₁
  simp [subst,h_closed₁]
  apply EvalStar.evalTrans
  apply Eval.evalAppRight
  constructor
  apply Eval.evalBeta
  apply h_val₂
  unfold Closed at h_closed₂
  simp [subst,h_closed₂]
  have h:subst "s" t₂ t₁ = t₁ := by 
    apply subst_closed
    unfold Closed 
    exact h_closed₁
  rw [h]
  apply EvalStar.evalTrans
  apply Eval.evalBeta
  constructor
  simp [subst]
  have h₂: ∀(t:Term), subst "p" t church_false = church_false := by 
    intro t 
    apply subst_closed 
    apply closed_tru
  rw [h₂]
  apply EvalStar.evalTrans
  apply Eval.evalBeta
  constructor
  simp [subst]
  have h₃: subst "b" church_false t₁ = t₁ := by 
    apply subst_closed 
    unfold Closed 
    exact h_closed₁ 
  rw [h₃]
  have h₄: subst "b" church_false t₂ = t₂ := by 
    apply subst_closed
    unfold Closed
    exact h_closed₂
  rw [h₄]
  apply app_fls
  apply h_val₁ 
  apply h_val₂ 
  unfold Closed 
  apply h_closed₁ 
  unfold Closed 
  apply h_closed₂
  
  def church_zero: Term := Term.Lambda "s" (Term.Lambda "z" (Term.Var "z"))
  def church_one: Term := Term.Lambda "s" (Term.Lambda "z" 
    (Term.App (Term.Var "s") (Term.Var "z")))
  def church_two: Term := Term.Lambda "s" (Term.Lambda "z" 
    (Term.App (Term.Var "s") (Term.App (Term.Var "s") (Term.Var "z"))))
  def church_three:Term :=  Term.Lambda "s" (Term.Lambda "z" 
    (Term.App (Term.Var "s") 
    (Term.App (Term.Var "s") (Term.App (Term.Var "s") (Term.Var "z")))))

  lemma zero_closed: Closed church_zero := by 
    simp [Closed,church_zero,free_vars]

  lemma one_closed: Closed church_one := by 
    simp [Closed,church_one,free_vars]

  def church_succ:Term := Term.Lambda "n" (Term.Lambda "s" (Term.Lambda "z" 
    (Term.App (Term.Var "s") 
    (Term.App (Term.App (Term.Var "n") (Term.Var "s")) (Term.Var "z")))))

  def church_plus: Term := Term.Lambda "m" (Term.Lambda "n" 
    (Term.Lambda "s" (Term.Lambda "z" 
      (Term.App 
        (Term.App (Term.Var "m") (Term.Var "s")) 
        (Term.App (Term.App (Term.Var "n") (Term.Var "s")) (Term.Var "z"))))))

  def church_times:Term := Term.Lambda "m" (Term.Lambda "n" 
    (Term.App 
      (Term.App (Term.Var "m") (Term.App church_plus (Term.Var "n")))
      church_zero))

  def church_pow:Term := Term.Lambda "m" (Term.Lambda "n" 
    (Term.App 
      (Term.App (Term.Var "m") (Term.App church_times (Term.Var "n")))
      church_one))

  def church_iszero: Term := Term.Lambda "m" 
    (Term.App (Term.App (Term.Var "m") (Term.Lambda "x" church_false)) church_true)

  lemma isz_one: EvalStar (Term.App church_iszero church_one) church_false := by 
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    have h := one_closed
    have h₂: subst "m" church_one church_false = church_false := by 
      simp [church_false,subst]
    have h₃: subst "m" church_one church_true = church_true := by 
      simp [church_true,subst]
    unfold Closed at h 
    simp [subst,h,h₂,h₃]
    apply EvalStar.evalTrans
    apply Eval.evalAppLeft
    apply Eval.evalBeta
    constructor
    have h₄:= closed_fls
    unfold Closed at h₄ 
    simp [subst,free_vars,h₄]
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    have h₅:=closed_tru
    unfold Closed at h₅ 
    have h₆: subst "z" church_true church_false = church_false := by 
      simp [church_false,subst]
    simp [subst,h₅,h₆]
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    have h₇: subst "x" church_true church_false = church_false := by 
      simp [church_false,subst]
    simp [h₇] 
    apply EvalStar.evalRefl

  lemma isz_zero: EvalStar (Term.App church_iszero church_zero) church_true := by 
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    have h:=zero_closed
    have h₁:=closed_fls
    have h₂: ∀ (t₂:Term) (v:String), subst v t₂ church_false = church_false := by 
      intro t₂ v
      apply subst_closed 
      exact h₁
    have h₃:=closed_tru
    have h₄: ∀ (t₂:Term) (v:String), subst v t₂ church_true = church_true := by 
      intro t₂ v
      apply subst_closed 
      exact h₃
    simp [subst,h,h₂,h₄]
    apply EvalStar.evalTrans
    apply Eval.evalAppLeft
    apply Eval.evalBeta
    constructor
    simp [subst]
    apply EvalStar.evalTrans
    apply Eval.evalBeta
    constructor
    simp [subst]
    apply EvalStar.evalRefl

  def church_zz: Term := Term.App (Term.App church_pair church_zero) church_zero
  def church_ss: Term := Term.Lambda "p" 
    (Term.App 
      (Term.App church_pair (Term.App church_snd (Term.Var "p")))
      (Term.App 
        (Term.App church_plus church_one)
        (Term.App church_snd (Term.Var "p"))))
  def church_pred: Term := Term.Lambda "m" (Term.App church_fst (Term.App (Term.App (Term.Var "m") church_ss) church_zz))

  def omega: Term := Term.App 
    (Term.Lambda "x" (Term.App (Term.Var "x") (Term.Var "x")))
    (Term.Lambda "x" (Term.App (Term.Var "x") (Term.Var "x")))


end UntypedLambda
