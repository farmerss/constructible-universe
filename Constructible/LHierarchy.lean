/-
Copyright (c) 2026 Farmer Schlutzenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Farmer Schlutzenberg, https://sites.google.com/site/schlutzenberg
-/
import Constructible.Basic

namespace LL
open LL
variable {α : Type u} {r : α → α → Prop} {h : IsWellOrder α r}

/-- Stub -/
def r_leq
  (x y : α)
:=
  --let i := h
  (r x y) ∨ (x=y)

/- Stub
instance r_leqIsPartialOrder (j : IsWellOrder α r) : IsPartialOrder α (r:=r_leq (r := r)) where
  refl := -- proof of: ∀ a, a ≤ a
    fun x => Or.inr (Eq.refl x)
  trans := -- proof of: ∀ a b c, a ≤ b → b ≤ c → a ≤ c
    by
    intros a b c hab hbc
    cases hab with
    | inl hab => --case r a b
      cases hbc with
      | inl hbc => --Case (r a b) ∧ (r b c)
        apply Or.inl
        exact IsStrictOrder.toIsTrans.trans a b c hab hbc
      | inr hbc => --Case (r a b) ∧ (b = c)
        subst hbc
        apply Or.inl
        exact hab
    | inr hab => --case a = b
      subst hab
      exact hbc
  antisymm := -- proof of: a ≤ b → b ≤ a → a = b
    by
    intro a b hab hba
    cases hab with
    | inl hab => --case r a b
      cases hba with
      | inl hba => --Case (r a b) ∧ (r b a)
        exact (j.wf.irrefl.irrefl a (IsStrictOrder.toIsTrans.trans a b a hab hba)).elim
      | inr hbc => --Case (r a b) ∧ (b = c)
        subst hbc
        exact Eq.refl b
    | inr hab => --case a = b
      subst hab
      exact Eq.refl a

/-- Stub -/
instance r_leqIsTotal (j : IsWellOrder α r) : Std.Total (r_leq (r := r)) where
  total a b :=
    by
      cases j.toTrichotomous.rel_or_eq_or_rel_swap (a:=a) (b:=b) with
      | inl hyp => apply Or.inl; apply Or.inl; exact hyp
      | inr hyp =>
      cases hyp with
      | inl hyp => subst hyp; apply Or.inl;
                   exact (r_leqIsPartialOrder (α:=α) (r := r) (j:=j)).refl a
      | inr hyp => apply Or.inr; apply Or.inl; exact hyp -- proof of: a ≤ b ∨ b ≤ a
-/

/-- Stub -/
theorem upper_bound
  {y a b : α}
  {h : IsWellOrder α r}
  (ha : r a y)
  (hb : r b y)
: ∃ (e:α), (r e y) ∧ ((h.linearOrder r).le a e ∧ (h.linearOrder r).le b e)
:=by
  cases h.toTrichotomous.rel_or_eq_or_rel_swap (a:=a) (b:=b) with
  | inl hyp => use b; exact ⟨hb,⟨Or.inr hyp,Or.inl (Eq.refl b)⟩⟩
  | inr hyp =>
  cases hyp with
  | inl hyp => use a; exact ⟨ha,⟨Or.inl (Eq.refl a),Or.inl hyp.symm⟩⟩
  | inr hyp => use a; exact ⟨ha,⟨Or.inl (Eq.refl a),Or.inr hyp⟩⟩

/-- Stub -/
theorem upper_bound_of_4
  {y a b c d : α}
  {h : IsWellOrder α r}
  (ha : r a y)
  (hb : r b y)
  (hc : r c y)
  (hd : r d y)
: ∃ (e : α), r e y
    ∧ ((h.linearOrder r).le a e)
    ∧ ((h.linearOrder r).le b e)
    ∧ ((h.linearOrder r).le c e)
    ∧ ((h.linearOrder r).le d e)
:=
  by
  cases upper_bound (h:=h) ha hb with
  | intro bound_ab hypab =>
  cases upper_bound (h:=h) hc hd with
  | intro bound_cd hypcd =>
  cases upper_bound (h:=h) hypab.1 hypcd.1 with
  | intro bound hyp =>
    use bound
    exact ⟨hyp.1,
      ⟨(h.linearOrder r).le_trans a bound_ab bound hypab.2.1 hyp.2.1,
      ⟨(h.linearOrder r).le_trans b bound_ab bound hypab.2.2 hyp.2.1,
      ⟨(h.linearOrder r).le_trans c bound_cd bound hypcd.2.1 hyp.2.2,
       (h.linearOrder r).le_trans d bound_cd bound hypcd.2.2 hyp.2.2⟩⟩⟩⟩

/-- Stub -/
theorem upper_bound_of_3
  {y a b c : α}
  {h : IsWellOrder α r}
  (ha : r a y)
  (hb : r b y)
  (hc : r c y)
: ∃ (d:α), r d y
    ∧ ((h.linearOrder r).le a d) ∧ ((h.linearOrder r).le b d) ∧ ((h.linearOrder r).le c d)
:=
  by
  rcases upper_bound_of_4 (h:=h) ha hb hc hc with ⟨e, hypey, hypae, hypbe, hypce, _⟩
  use e

mutual
/--
Our definition of the constructible universe $L$ and its levels $L_γ$
for ordinals $γ$ proceeds technically slightly differently to the usual one.

Recall that in the usual one, $L_0=∅$, $L_{γ+1}=P_d(L_γ)$ where $P_d$ is the "definable power set",
that is, the set of all subsets of $L_γ$ which are definable over $L_γ$ in the language
of set theory from parameters in $L_γ$, and taking unions at limit stages $λ$, so $L_λ=⋃_{γ<λ}L_γ$.
The definition of $L_γ$ is usually made by recursion on ordinals $γ$.

Instead of fully defining each level $L_γ$ by recursion on $γ$,
we will first define, for a given ordinal $γ$, the set of all *codes for elements of $L_γ$*.
This itself will be a recursion on $γ$, given through the definition
of the inductive type `L_code_below` below. Having defined these codes,
we will, by another recursion (a wellfounded recursion), define the
models $L_γ$ themselves. (Actually the model we define won't have true equality as its
notion of equality, but an equivalence relation. Modulo that, it will be isomorphic to $L_γ$.
It will also be defined relative to a given wellorder of ordertype $γ$.
In fact, what does $L_γ$ really mean at this point?)

The following is the type giving codes $c$ for constructible sets $X$.
They consist of:\
(1) an ordinal $γ$ (the "`y`" in the code below),
    specifying that $X$ will be in $L_{γ+1}$; $γ$ will be the "rank" of $c$,\
(2) a formula $ϕ$ (`φ : LSTF`),\
(3) a variable $v$ (`v : var`),\
(4) a map $ρ$ from the free variables of $φ$ excluding $v$ to codes of rank $< γ$.\
Then $c$ codes $$X_c= {v ∈ L_γ | L_γ \models φ(v,X_{ρ(v_1)},...X_{ρ(v_k)})}.$$
Note here that $X_{ρ(v_i)}$ (the set coded by $ρ(v_i)$) is in $L_γ$, by induction,
$v$ (the variable bound in the definition of $X_c$) was specified in (3),
and $v_1,...,v_k$ are supposed to enumerate the free variables of $φ$ excluding $v$.
($v$ itself might not actually appear in $φ$.)

The main type of code is those of type `L_code`. The `y` there corresponds to the rank $γ$
of the code. We work with an arbtirary wellordering `r` of a type `α` to give our indices
for building the $L$-hierarchy, so `y:α`. A secondary type is `L_code_below`; this specifies
both a bound `x`, and `y` with `r y x` (with a proof of this), and an `L_code` at rank `y`.
There are also lists of these `L_code_below` objects, which we use as the list of parameters
used in building a code of type `L_code`.

Note that when $x$ is "$0$"; that is, the `r`-least element of `α`,
there is a unique element of type `L_List r h x`, which is just the empty list `List.nil`.
This is the list of all codes for elements of $L_0=∅$.

The general parameters for the types will be `(α:Type u)`, `(r:α→α→ Prop)` and
`(h:IsWellOrder α r)`.

The first type to be defined mutually is `L_list (x:α) (n:Nat)`,
that of "lists" of length `n` consisting of objects of type `L_bound_code (x:α)`, defined below,
which consist of some `(y:α)` with `r y x`, and an `L_code y` (also defined below).
We implement the lists manually, in order to get around issues
with getting the recursion to be accepted by Lean. -/
  inductive L_List
  : (x : α) → (n : Nat) → Type u --(x : α) is the strict upper bound for allowed
                                 --ranks of codes in list, n:Nat is the length of the list
  where
  | nil :
      {x:α} →
      L_List x 0 -- output type (length 0, empty list)
  | cons :
      {x:α} → -- bound for head of list
      (L_code_below x) → -- head of list (recursive argument)
      {n:Nat} → -- length of tail
      (L_List x n) → -- tail of list
      L_List x (n+1) -- output type of "cons" constructor

/-- The second type mutually defined is `L_code (y:α)`, that of codes
for elements of the "definable power set" $P_d(L_y)$ of $L_y$. -/
  inductive L_code
  : (y : α) → Type u -- y is specifies the rank of the code
  where
  | code :
      {y : α} →
      (φ : LSTF) →
      (v : var) →
      (σ : List var) →
      (hσ : σ.Nodup ∧ σ ≈ (free_var_excluding φ v)) →
      (τ : L_List y σ.length) → --note this is a recursive argument
      L_code y --output type

/-- The third type defined mutually is that of `L_code_below (x:α)`, consisting of
 some `y` with `r y x`, and some element of `L_code y`. -/
  inductive L_code_below
  : (x : α) → Type u
  where
  | boundcode :
      {x : α} →
      (y : α) →
      (hryx : r y x) →
      (code : L_code y) →
      L_code_below x  -- output type
end

namespace L_List

/-- Stub. I could have just output `n` instead of using `τ` to define the length.
But this leads to problems with the linter complaining of unused arguments.
But I want to define `τ.length` here, so I want `τ` as an argument. -/
def length
  {x : α}
  {n : Nat}
  (τ : L_List (r := r) x n)
: Nat
:= match τ with
| .nil => 0
| .cons _ (n:=k) _ => k + 1

end L_List

/-- Stub -/
theorem L_List_length_cons_x_nil
  {x : α}
  (y : L_code_below (r := r) x)
: (L_List.cons y L_List.nil).length = 1
:= rfl

theorem L_List_length
  {x : α}
  {m : Nat}
  {τ : L_List (r := r) x m}
: τ.length = m
:=match τ with
  | .nil => rfl
  | .cons _ (n:=k) _ => rfl

/-- Definition: `to_List` converts an object of type `L_List` to a standard list type. -/
def to_List
  {x : α}
  {n : Nat}
  (τ : L_List (r := r) x n)
:  List (L_code_below (r := r) x)
:=
  match n, τ with
  | 0, L_List.nil (r := r)  => List.nil
  | _ + 1, L_List.cons c τ' => List.cons c (to_List τ')

/-- Theorem: The casting of `L_List` to `List` given by `to_List`
respects "cons". -/
theorem L_ListToListConsCons
  {x : α}
  {n : Nat}
  (τ : L_List (r := r) x n)
  (c : L_code_below x)
: to_List (L_List.cons c τ) = List.cons c (to_List τ)
:= rfl

/-- Theorem: The index `(n:Nat)` for an `L_List` object is just the length
of its associated List object provided by `to_List`. -/
theorem L_ListToListLength
  {x : α}
  {n : Nat}
  (τ : L_List (r := r) x n)
: (to_List τ).length = τ.length
:=
  --have i : τ.length = n := by rfl
  by
    rw [L_List_length]
    match n, τ with
    | 0, L_List.nil  => rfl
    | m + 1, L_List.cons c τ' =>
      rw [L_ListToListConsCons]
      rw [List.length_cons]
      rw [L_ListToListLength τ']
      rw [L_List_length]

end LL

/-- Definition: `build_ass` builds an `assignment M φ` object from input data coming
from an `L_code` object together with some `x:M.univ` to interpret the excluded variable `v`
(and the relevant proofs). -/
def build_ass
  (M : LSTModel.{u})
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (hσ : σ.Nodup ∧ σ ≈ (free_var_excluding φ v))
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
: assignment M φ
:=
  if i : v ∈ free_var φ then
    assignment.mk
      (keys := (v::σ))
      -- Proof of `keys.Nodup`: we argue roughly as follows:
      -- `v ∉ σ`, since `σ ≈ free_varExc φ v`, and since `σ.Nodup` and `v ∉ σ`,
      --therefore `(cons v σ).Nodup`.
      --
      -- In more detail:
      -- `(List.Nodup.cons (α := var) (l := σ) (a := v) (hv : v∉σ) (hσ : σ.Nodup))`
      -- `: (cons v σ).Nodup`
      --
      -- To get `hv`, we use:
      -- `excluded_var_notin_free_var_excluding (φ:LSTF) (v:var)`
      -- `: v ∉ free_var_excluding φ v`
      -- together with
      -- `(List_mem_respects_ext_equiv (α:=var) σ (free_var_excluding φ v) hσ.2 v).mp.mt`
      -- `: (v ∉ free_var_excluding φ v) → v ∉ σ`
      --
      -- ().mpr ass
      (hNodup := (List.Nodup.cons
                 (α:=var)
                 (l:=σ)
                 (a:=v)
                 --Proof that `v ∉ σ`:
                 ((List_mem_respects_ext_equiv
                    (α:=var) σ (free_var_excluding φ v) hσ.2 v).mp.mt
                  (excluded_var_notin_free_var_excluding φ v))
                 --Proof that `σ.Nodup`
                 hσ.1))
      --Proof of `keys ≈ free_var φ`
      --We have `(v :: free_var_excluding φ v) ≈ free_var φ`, by
      --theorem `cons_free_var_excluding_ext_equiv_free_var (φ:LSTF) (v:var) (h: v ∈ free_var φ)`
      -- `: (v :: (free_var_excluding φ v)) ≈ free_var φ`
      --And have `(v :: σ) ≈ (v :: free_var_excluding φ v)` by
      --theorem `cons_respects_ext_equiv (s t : List α)  (h : s ≈ t)  (x:α)`
      -- `: (x::s) ≈ (x::t)`
      --So we can use transitivity of `≈`
      (hfree_var := Setoid.trans
                  (List_cons_respects_ext_equiv var v hσ.2)
                  (cons_free_var_excluding_ext_equiv_free_var φ v i))
      (values := (x::τ))
      (hvalues := cons_preserves_length_equality (α:=var) (β:= M.univ) v σ x τ hτ)
  else
    --Case `v ∉ free_var φ`: Here we almost have everything needed already.
    --The main thing is the proof that `keys ≈ free_var φ`, for which we use
    -- theorem `free_var_excluding_is_free_var_if_excluded_not_present (φ:LSTF) (v:var)
    --(h: v ∉ free_var φ) : free_var_excluding φ v ≈ free_var φ`
    assignment.mk
      σ hσ.1 (Setoid.trans hσ.2 (free_var_excluding_is_free_var_if_excluded_not_present φ v i)) τ hτ

/-- Stub -/
theorem excluded_var_in_free_var_build_ass_keys_eq_cons
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : v ∈ free_var φ)
: (build_ass M φ v σ h τ hτ x).keys = (v :: σ)
:=
  by
  unfold build_ass
  simp only [i, ↓reduceDIte]
--Alternate proof:
-- unfold build_ass
--  split
--  · rfl
--  · contradiction

/-- Stub -/
theorem excluded_var_in_free_var_build_ass_values_eq_cons
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : v ∈ free_var φ)
: (build_ass M φ v σ h τ hτ x).values = (x::τ)
:=
  by
  unfold build_ass
  simp only [i, ↓reduceDIte]

/-- Stub -/
theorem length_values_build_ass_on_new_var_positive
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : v ∈ free_var φ)
: 0 < (build_ass M φ v σ h τ hτ x).values.length
:=
  by
  let ass := (build_ass M φ v σ h τ hτ x)
  have k : ass = build_ass M φ v σ h τ hτ x := by rfl
  have  j' : (build_ass M φ v σ h τ hτ x).values = (x::τ) :=
    by
    unfold build_ass
    simp [i]
  have l' : ass.values = (x::τ) :=
    by
    rw [← k] at j'
    exact j'
  have m : ass.values.length = τ.length + 1 := by rw[l']; rfl
  have n : 0 < ass.values.length := by simp [m]
  exact n

/-- Stub -/
theorem eval_build_ass_has_old_vars_mem_keys
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (w : var)
  (hw : w ∈ free_var φ)
: w ∈ (build_ass M φ v σ h τ hτ x).keys
:=(build_ass M φ v σ h τ hτ x).hfree_var.2 hw

/-- Stub -/
theorem eval_build_ass_on_new_var_has_new_var_mem_keys
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : v ∈ free_var φ)
: v ∈ (build_ass M φ v σ h τ hτ x).keys
:=
  by
  have  j : (build_ass M φ v σ h τ hτ x).keys = (v::σ) :=
    by
    unfold build_ass
    simp [i]
  have k : v ∈ (v::σ) := List.mem_cons_self
  rw [← j] at k
  exact k

/-- Stub -/
theorem there_exists_proof_eval_build_ass_on_new_var_has_new_var_mem_keys
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : v ∈ free_var φ)
:  v ∈ (build_ass M φ v σ h τ hτ x).keys
:=
  by
  use (eval_build_ass_on_new_var_has_new_var_mem_keys M φ v σ h τ hτ x i)

/-- Stub -/
theorem new_var_in_free_var_in_build_ass_keys
  --{α : Type u}
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : v ∈ free_var φ)
:  v ∈ (build_ass M φ v σ h τ hτ x).keys
:=
  by
  rw [excluded_var_in_free_var_build_ass_keys_eq_cons M φ v σ h τ hτ x i]
  exact List.mem_cons_self (a:=v) (l:=σ)

/-- Stub -/
theorem eval_build_ass_on_new_var
  --{α : Type u}
  (M : LSTModel)
  (φ : LSTF)
  (v : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : v ∈ free_var φ)
  (hkeys : v ∈ (build_ass M φ v σ h τ hτ x).keys
  := new_var_in_free_var_in_build_ass_keys M φ v σ h τ hτ x i)
: var_eval (build_ass M φ v σ h τ hτ x) v hkeys = x
:=
  by
  unfold var_eval
  dsimp only [Lean.Elab.WF.paramLet]
  have  j_keys : (build_ass M φ v σ h τ hτ x).keys = (v::σ)
  := excluded_var_in_free_var_build_ass_keys_eq_cons M φ v σ h τ hτ x i
  have  j_values : (build_ass M φ v σ h τ hτ x).values = (x::τ)
  := excluded_var_in_free_var_build_ass_values_eq_cons M φ v σ h τ hτ x i
  have m
  : List.idxOf v (build_ass M φ v σ h τ hτ x).keys = 0
  := by rw[j_keys]; simp only [List.idxOf_cons_self]
  have o : 0 < (build_ass M φ v σ h τ hτ x).values.length
  := length_values_build_ass_on_new_var_positive M φ v σ h τ hτ x i
  have n : value_at_index (build_ass M φ v σ h τ hτ x).values 0 o = x
  := by simp only [j_values]; rfl
  simp only [m]
  exact n

/-- Stub -/
def eval_var_param_pair
  {β : Type u}
  (σ : List var)
  (τ : List β)
  (hτ : σ.length = τ.length)
  (v : var)
  (i : v ∈ σ)
: β
:=
  let idv := σ.idxOf v
  let idv_lt_length_keys : idv < σ.length := List.idxOf_lt_length_iff.mpr i
  let idv_lt_length_values : idv < τ.length := hτ ▸ idv_lt_length_keys
  value_at_index τ idv idv_lt_length_values

/-- Stub -/
theorem eval_var_param_cons_pair_on_old_var
  {β : Type u}
  (σ : List var)
  --(hσ : σ.Nodup)
  (τ : List β)
  (hτ : σ.length = τ.length)
  (w : var)
  (i : w ∈ σ)
  (v : var)
  (j : v ∉ σ)
  (x : β)
: eval_var_param_pair
    (v::σ)
    (x::τ)
    --proof of (v::σ).length = (x::τ).length:
    (by simp only [(List.length_cons (a:=v) (as:=σ)),
                   List.length_cons,
                   Nat.add_right_cancel_iff];
                  exact hτ)
    w
    (List.mem_cons_of_mem v i : w ∈ (v::σ))
= eval_var_param_pair σ τ hτ w i
:=
  by
  unfold eval_var_param_pair
  dsimp
  let idxσ := σ.idxOf w
  let idxvσ := (v::σ).idxOf w
  have k : v ≠ w :=
    by
    intro k
    rw[k] at j
    contradiction
  have l : idxσ < σ.length := List.idxOf_lt_length_iff.mpr i
  have n : (v::σ).idxOf w  = σ.idxOf w + 1
  := List.idxOf_cons_ne σ k
  simp only [n]
  exact value_at_succ_index_of_cons τ (σ.idxOf w) (hτ.symm ▸ l) x

/-- Stub -/
theorem eval_build_ass_on_old_var
  (M : LSTModel)
  (φ : LSTF)
  (v w : var)
  (σ : List var)
  (h : σ.Nodup ∧ σ ≈ free_var_excluding φ v)
  (τ : List M.univ)
  (hτ : σ.length = τ.length)
  (x : M.univ)
  (i : w ∈ σ)
  (h_w_in_keys : w ∈ (build_ass M φ v σ h τ hτ x).keys
  :=
    eval_build_ass_has_old_vars_mem_keys M φ v σ h τ hτ x w
      --proof that w ∈ free_var φ: use w ∈ σ ≈ free_var_excluding φ v ⊆ free_var φ
      --proof that w ∈ (free_var_excluding φ v)
      --  := (List_mem_respects_ext_equiv_mp var σ (free_var_excluding φ v) h.2 i)
      --proof that free_var_excluding φ v ⊆ free_var φ := free_var_excluding_is_sub_free_var φ v
      (free_var_excluding_is_sub_free_var φ v
        (List_mem_respects_ext_equiv_mp var σ (free_var_excluding φ v) h.2 w i)))
: var_eval (build_ass M φ v σ h τ hτ x) w h_w_in_keys =
  eval_var_param_pair σ τ hτ w i
:=
  by
  let ass := build_ass M φ v σ h τ hτ x
  unfold var_eval
  unfold eval_var_param_pair
  dsimp only
  unfold build_ass
  split
  · dsimp only
    have h_idxOf_w_lt_length_tau
    : (List.idxOf w σ) < τ.length
    := (hτ ▸ ((List.idxOf_lt_length_iff (l:=σ) (a:=w)).mpr i))
    have h_succ_idxOf_w_lt_length_cons_x_tau
    : (List.idxOf w σ).succ < (x::τ).length
    := Nat.succ_lt_succ h_idxOf_w_lt_length_tau
    have goal_but_with_succ
    :   value_at_index τ (List.idxOf w σ) h_idxOf_w_lt_length_tau
      = value_at_index (x::τ) (List.idxOf w σ).succ h_succ_idxOf_w_lt_length_cons_x_tau
    :=  value_at_index_of_cons_at_succ_eq_value_at_index
          τ (List.idxOf w σ) h_idxOf_w_lt_length_tau x
    have
    :   List.idxOf w (v::σ) = (List.idxOf w σ).succ
    :=  List.idxOf_cons_ne
          σ (variable_in_free_var_excluding_is_neq_excluded_var φ v w (h.2.1 i)).symm
    rw [goal_but_with_succ]
    congr 1
  · dsimp only

--Some helper objects to define lift_code operation below.
-- `v_5` is some specific variable
-- `v_6` is another one
-- `φ_5` says $v_6 ∈ v_5$
-- `σ_5 = [v_6]`, so `[v_6] = free_var_excluding φ_5 v_5`
-- `hσ_5` : the correctness statement

/-- Stub -/
def v₀ : var := var.mk 0

/-- Stub -/
def v₁ : var := var.mk 1

/-- Stub -/
def v₂ : var := var.mk 2

/-- Stub -/
def v₃ : var := var.mk 3

/-- Stub -/
def v₄ : var := var.mk 4

/-- Stub -/
def v₅ : var := var.mk 5

/-- Stub -/
def v₆ : var := var.mk 6

/-- Stub -/
def φ₅ : LSTF := LSTF.atomic_mem v₅ v₆

/-- Stub -/
def σ₅ : List var := [v₆]

/-- Stub -/
lemma hσ₅ :σ₅.Nodup ∧ σ₅ ≈ (free_var_excluding φ₅ v₅) := by
  apply And.intro
  · apply List.nodup_singleton
  · rw [free_var_excluding_is φ₅ v₅]
    unfold φ₅
    unfold free_var
    unfold σ₅
    have h : 5≠ 6 := by simp
    have i : var.mk 5 ≠ var.mk 6 := var.mk.inj.mt h
    unfold v₅
    unfold v₆
    have j
    : (insert (var.mk 5) (insert (var.mk 6) ∅):List var).erase (var.mk 5) = ({var.mk 6}:List var)
    := List.erase_cons_head (var.mk 5) ({var.mk 6}:List var)
    rw [j]
    have k : [var.mk 6] = ({var.mk 6}:List var) := by rfl
    rw[k]

/-- Stub -/
lemma hσ₅length : σ₅.length = 1 := by rfl

/-- Stub -/
lemma v₅_mem_free_var_φ₅ : v₅ ∈ free_var φ₅ := first_in_free_var_atomic_mem v₅ v₆

/-- Stub -/
lemma v₆_mem_free_var_φ₅ : v₆ ∈ free_var φ₅ := second_in_free_var_atomic_mem v₅ v₆

/-- Stub -/
lemma v₆_mem_σ₅ : v₆ ∈ σ₅ := List.mem_singleton_self v₆

namespace LL

variable {α : Type u} {r : α → α → Prop} {h : IsWellOrder α r}

/-- Given an `c : L_code` of rank `y` and `y'` with `r y y'`, there is a canonical
lift of `c` to an `c' : L_code` of rank `y'`, for the same object:
just set `c'` to be the code of rank `y'` that uses the parameter $X_c$ (the interpretation of `c`)
to define itself, as the set of its members.
So `c'` uses the formula $v_6 ∈ v_5$ for some variables `v_5`, `v_6`,
interpreting `v_5` as $X_c$ and leaving `v_6` free. This is implemented by
 `lift_code`. -/
def lift_code
  (y1 y2 : α)
  (h' : r y1 y2)
  (code : L_code (r := r) y1)
: L_code (r := r) y2
:= L_code.code φ₅ v₅ σ₅ hσ₅ (L_List.cons (L_code_below.boundcode y1 h' code) L_List.nil)

/-- Stub -/
abbrev L_univ
 (x : α)
:= L_code_below (r := r) x

/-- Stub -/
structure LSTInterpretation
  (x : α)
where
  /-- field of `LSTInterpretation`: a binary relation on the class `L_univ x` of codes
  for elements of $L_γ$, where $γ$ is the ordinal at rank $x$. This is intended as the
  the "equality" (equivalence) relation over these codes. -/
  equiv : (L_univ (r := r) x) → (L_univ (r := r) x) → Prop
  /-- field of `LSTInterpretation`: a binary relation on the class `L_univ x` of codes
  for elements of $L_γ$, where $γ$ is the ordinal at rank $x$. This is intended as the
  the "membership" relation over these codes. -/
  mem : (L_univ (r := r) x) → (L_univ (r := r) x) → Prop

/-- Stub -/
def sats_L_code_param
  {y : α}
  (int : LSTInterpretation (r := r) y)
  (c : L_code (r := r) y)
  (x : L_univ (r := r) y)
: Prop
:=
  let M := LSTModel.mk (L_univ y) int.equiv int.mem
  match c with
  | L_code.code φ v σ hσ τ =>
    let hτ : σ.length = (to_List τ).length := Eq.trans L_List_length.symm
                                                       (L_ListToListLength τ).symm
    sats M φ (build_ass M φ v σ hσ (to_List τ) hτ x)

/-- This takes as input a model with universe the `y`-bounded `L_code_below`s for
some `y`, `r`, `h`, and given equality and membership relations (`eq`, `mem`),
and two codes for subsets of it, and checks whether they define the same set. -/
def code_equiv
  {y : α}
  (int : LSTInterpretation (r := r) y)
  (c c' : L_code (r := r) y)
: Prop
:=
  ∀ (x : L_univ y),
    (sats_L_code_param int c x)  ↔ (sats_L_code_param int c' x)

/-- This takes as input a model with universe the `y`-bounded `L_code_below`s for some
`y`, `r`, `h`, and given equality and membership relations (`eq`, `mem`),
and two codes for subsets of it, and checks whether the first codes an element of the second. -/
def code_mem
  {y : α}
  (int : LSTInterpretation (r := r) y)
  (c c' : L_code (r := r) y)
: Prop
:=
  ∃ (p:L_univ y), --p will be the set coded by c, and will be in the set coded by c'
    (∀ (x:L_univ y),
        (sats_L_code_param int c x)
      ↔ (int.mem x p))
    ∧ (sats_L_code_param int c' p)

/-- Stub -/
theorem code_equiv_is_Equivalence
  (y : α)
  (int : LSTInterpretation (r := r) y)
: Equivalence (code_equiv (α:=α) int)
  where
    refl (c : L_code (r := r) y) :=
      by
      unfold code_equiv
      exact fun x => Iff.rfl
    symm
      {c d : L_code y}
      (i : code_equiv int c d)
    :=
      by
      unfold code_equiv
      unfold code_equiv at i
      exact fun x => (i x).symm
    trans
      {c d e : L_code y}
      (hcd : code_equiv int c d)
      (hde : code_equiv int d e)
    :=
      by
      unfold code_equiv
      unfold code_equiv at hcd hde
      exact fun x => Iff.trans (hcd x) (hde x)

/-- Stub -/
theorem code_mem_respects_code_equiv
  {y : α}
  (int : LSTInterpretation (r := r) y)
  {c c' : L_code (r := r) y}
  {d d' : L_code (r := r) y}
  (hcc' : code_equiv int c c')
  (hdd' : code_equiv int d d')
: (code_mem int c d) → (code_mem int c' d')
:=
  by
  intro hyp
  unfold code_mem at hyp
  unfold code_mem
  cases hyp with
  | intro p hyp =>
    use p
    apply And.intro
    · --proof that X_{c'} = p
      intro x
      exact Iff.trans (hcc' x).symm (hyp.1 x)
    · --proof that p is in X_{d'}
      unfold code_equiv at hdd'
      exact (hdd' p).mp hyp.2

/-- Stub -/
theorem code_mem_respects_code_equiv_iff
  {y : α}
  (int : LSTInterpretation (r := r) y)
  {c c' : L_code (r := r) y}
  {d d' : L_code (r := r) y}
  (hcc' : code_equiv int c c')
  (hdd' : code_equiv int d d')
:  (code_mem int c d) ↔ (code_mem int c' d')
:= Iff.intro (code_mem_respects_code_equiv int hcc' hdd')
             (code_mem_respects_code_equiv int ((code_equiv_is_Equivalence y int).symm hcc')
                                               ((code_equiv_is_Equivalence y int).symm hdd'))

/-- Stub -/
def L_recursion_trichotomy_equiv_general
  (x : α)
  (lx : (y : α) → (_ : r y x) → LSTInterpretation (r := r) y)
  (y1 : α)
  (h1 : r y1 x)
  (code1 : L_code (r := r) y1)
  (y2 : α)
  (h2 : r y2 x)
  (code2 : L_code (r := r) y2)
: Prop
:=
    (∃ (h' : r y1 y2), code_equiv (lx y2 h2) (lift_code y1 y2 h' code1) code2)
  ∨ (∃ (h' : r y2 y1), code_equiv  (lx y1 h1) code1 (lift_code y2 y1 h' code2))
  ∨ (∃ (h' : y1=y2),  code_equiv  (lx y1 h1) code1 (h'▸code2))

/-- Stub -/
def L_recursion_trichotomy_mem_general
  (x : α)
  (lx : (y : α) → (_ : r y x) → LSTInterpretation (r := r) y)
  (y1 : α)
  (h1 : r y1 x)
  (code1 : L_code (r := r) y1)
  (y2 : α)
  (h2 : r y2 x)
  (code2 : L_code (r := r) y2)
: Prop
:=
    (∃ (h' : r y1 y2), code_mem (lx y2 h2) (lift_code y1 y2 h' code1) code2)
  ∨ (∃ (h' : r y2 y1), code_mem  (lx y1 h1) code1 (lift_code y2 y1 h' code2))
  ∨ (∃ (h' : y1=y2),  code_mem  (lx y1 h1) code1 (h'▸code2))

/-- Here is the recursion defining $L_x$, relative to a wellorder `r` on a type `α`,
and `x : α`.
The main issue is to define the second argument to `WellFounded.fix`,
which is the recursion defining $L_x$ from $(x,lx=(L_y)_{r y x})$.

`(lx y h)` should be a pair `(eq, mem)`  such that
`eq` is an equivalence relation on the type `T_y = (CodeBelowBound r h y)`
(so `eq : T_y → T_y → Prop`)
and `mem` is a binary relation on that type which respects `eq`
(so also `mem : T_y → T_y → Prop`),
and if `r z y` then considering the natural embedding `π_{zy}`
of `L_code_below r h z` into `L_code_below r h y`
(which just replaces the "upper bound" `z` with `y` and corresponding proof in the
constructor's arguments) then `eq_y`, `mem_y` agrees with `eq_z`, `mem_z` on those elements.

So we have to now define `eq_x` and `mem_x`.
Given two codes `c`, `d` of the relevant type (`L_code_below r h x`),
if the non-bounded codes have the same rank `y` (where `r y x`),
we do a computation over $L_y$ to compute equivalence and membership.
If the non-bounded codes have ranks `z` where `r z y` (where `r y x`),
then we convert the rank `z` code to a rank `y` code in the canonical fashion,
and then use the method of the previous case. -/
def L_recursion
: (x : α) → (lx:(y : α) → r y x → (LSTInterpretation (r := r) y))
 →  (LSTInterpretation (r := r) x)
:= fun (x : α)  (lx: (y : α) → r y x →  (LSTInterpretation (r := r) y))
 =>
    LSTInterpretation.mk
      --equivalence relation `eq_x`:
      (fun (c1 c2 : L_code_below  x) =>
         match c1 with
         | L_code_below.boundcode y1 h1 code1 =>
         match c2 with
         | L_code_below.boundcode y2 h2 code2 =>
           L_recursion_trichotomy_equiv_general x lx y1 h1 code1 y2 h2 code2
      )
      --membership relation `mem_x`:
      (fun (c1 c2 : L_code_below x) =>
         match c1 with
         | L_code_below.boundcode y1 h1 code1 =>
         match c2 with
         | L_code_below.boundcode y2 h2 code2 =>
           L_recursion_trichotomy_mem_general x lx y1 h1 code1 y2 h2 code2
      )

/-- Stub -/
noncomputable def L
: (x : α) → LSTInterpretation (r := r) x
:= WellFounded.fix h.wf (L_recursion)

/-- Stub -/
noncomputable def L_Model
: (x : α) → LSTModel
:= fun (x:α) => LSTModel.mk (L_univ (r := r) x) (L (h:=h) x).equiv (L (h:=h) x).mem

/-- Stub -/
@[nolint unusedArguments]
noncomputable def L_hierarchy_below
(x : α)
: (y:α)→ r y x → LSTInterpretation (r := r) y
:= fun (y:α) (_h : r y x) => L (h:=h) y

/-- Stub -/
theorem L_fixed_point_of_recursion
  (x : α)
: L (h:=h) x = (L_recursion x) (L_hierarchy_below (h:=h) x)
:= WellFounded.fix_eq h.wf L_recursion x

/-- Stub -/
theorem L_seg_equiv_via_general
  (x : α)
  (c1 c2 : L_code_below x)
: (L (h:=h) x).equiv c1 c2 ↔
  (match c1 with
  | L_code_below.boundcode y1 h1 code1 =>
  match c2 with
  | L_code_below.boundcode y2 h2 code2 =>
    L_recursion_trichotomy_equiv_general
      x (L_hierarchy_below (h:=h) x) y1 h1 code1 y2 h2 code2)
:=
  by
  have j : ((L (h:=h) x).equiv c1 c2)
  ↔ (((L_recursion x) (L_hierarchy_below (h:=h) x)).equiv c1 c2)
  :=
    by
    rw[L_fixed_point_of_recursion x]
  rw [j]
  unfold L_recursion
  dsimp
  rfl

/-- Stub -/
theorem L_seg_mem_via_general
  (x : α)
  (c1 c2 : L_code_below x)
: (L (h:=h) x).mem c1 c2 ↔
  (match c1 with
  | L_code_below.boundcode y1 h1 code1 =>
  match c2 with
  | L_code_below.boundcode y2 h2 code2 =>
    L_recursion_trichotomy_mem_general
      x (L_hierarchy_below (h:=h) x) y1 h1 code1 y2 h2 code2)
:=
  by
  have j : ((L (h:=h) x).mem c1 c2)
  ↔ (((L_recursion x) (L_hierarchy_below (h:=h) x)).mem c1 c2)
  :=
    by
    rw[L_fixed_point_of_recursion x]
  rw [j]
  unfold L_recursion
  dsimp only
  rfl

/-- Stub -/
def L_recursion_trichotomy_equiv
--(x : α)
(y1 : α)
--(_ : r y1 x)
(code1 : L_code (r := r) y1)
(y2 : α)
--(_ : r y2 x)
(code2 : L_code (r := r) y2)
: Prop
:= (∃ (h' : r y1 y2), code_equiv (L (h:=h) y2) (lift_code y1 y2 h' code1) code2)
∨ (∃ (h' : r y2 y1), code_equiv  (L (h:=h) y1) code1 (lift_code y2 y1 h' code2))
∨ (∃ (h' : y1=y2),  code_equiv  (L (h:=h) y1) code1 (h'▸code2))

/-- Stub -/
def L_recursion_trichotomy_mem
--(x : α)
(y1 : α)
--(_ : r y1 x)
(code1 : L_code (r := r) y1)
(y2 : α)
--(_ : r y2 x)
(code2 : L_code (r := r) y2)
: Prop
:= (∃ (h' : r y1 y2), code_mem (L (h:=h) y2) (lift_code y1 y2 h' code1) code2)
∨ (∃ (h' : r y2 y1), code_mem (L (h:=h) y1) code1 (lift_code y2 y1 h' code2))
∨ (∃ (h' : y1=y2),  code_mem (L (h:=h) y1) code1 (h'▸code2))

/-- Stub -/
theorem L_recursion_trichotomy_mem_first_lt_second
--(x : α)
(y1 : α)
--(h1 : r y1 x)
(code1 : L_code (r := r) y1)
(y2 : α)
--(h2 : r y2 x)
(code2 : L_code (r := r) y2)
(h12 : r y1 y2)
: (L_recursion_trichotomy_mem (h:=h) y1 code1 y2 code2)
↔  code_mem (L (h:=h) y2) (lift_code y1 y2 h12 code1) code2
:=
  by
  apply Iff.intro
  · intro hyp
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact hyp'
    | inr hyp =>
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' =>
        exact (h.wf.irrefl.irrefl y1 (IsStrictOrder.toIsTrans.trans y1 y2 y1 h12 h')).elim
    | inr hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 (h'▸ h12)).elim
  · intro hyp
    apply Or.inl
    use h12

/-- Stub -/
theorem L_recursion_trichotomy_equiv_first_lt_second
--(x : α)
(y1 : α)
--(h1 : r y1 x)
(code1 : L_code (r := r) y1)
(y2 : α)
--(h2 : r y2 x)
(code2 : L_code (r := r) y2)
(h12 : r y1 y2)
: (L_recursion_trichotomy_equiv (h:=h) y1 code1 y2 code2)
↔  code_equiv (L (h:=h) y2) (lift_code y1 y2 h12 code1) code2
:=
  by
  apply Iff.intro
  · intro hyp
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact hyp'
    | inr hyp =>
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' =>
        exact (h.wf.irrefl.irrefl y1 (IsStrictOrder.toIsTrans.trans y1 y2 y1 h12 h')).elim
    | inr hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 (h'▸ h12)).elim
  · intro hyp
    apply Or.inl
    use h12

/-- Stub -/
theorem L_recursion_trichotomy_mem_second_lt_first
--(x : α)
(y1 : α)
--(h1 : r y1 x)
(code1 : L_code (r := r) y1)
(y2 : α)
--(h2 : r y2 x)
(code2 : L_code (r := r) y2)
(h12 : r y2 y1)
: (L_recursion_trichotomy_mem (h:=h) y1 code1 y2 code2)
↔  code_mem (L (h:=h) y1) code1 (lift_code y2 y1 h12 code2)
:=
  by
  apply Iff.intro
  · intro hyp
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' =>
        exact (h.wf.irrefl.irrefl y2 (IsStrictOrder.toIsTrans.trans y2 y1 y2 h12 h')).elim
    | inr hyp =>
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact hyp'
    | inr hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 (h'▸ h12)).elim
  · intro hyp
    apply Or.inr
    apply Or.inl
    use h12

/-- Stub -/
theorem L_recursion_trichotomy_equiv_second_lt_first
--(x : α)
(y1 : α)
--(h1 : r y1 x)
(code1 : L_code (r := r) y1)
(y2 : α)
--(h2 : r y2 x)
(code2 : L_code (r := r) y2)
(h12 : r y2 y1)
: (L_recursion_trichotomy_equiv (h:=h) y1 code1 y2 code2)
↔  code_equiv (L (h:=h) y1) code1 (lift_code y2 y1 h12 code2)
:=
  by
  apply Iff.intro
  · intro hyp
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' =>
        exact (h.wf.irrefl.irrefl y2 (IsStrictOrder.toIsTrans.trans y2 y1 y2 h12 h')).elim
    | inr hyp =>
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact hyp'
    | inr hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 (h'▸ h12)).elim
  · intro hyp
    apply Or.inr
    apply Or.inl
    use h12

/-- Stub -/
theorem L_recursion_trichotomy_mem_first_eq_second
--(x : α)
(y1 : α)
--(h1 : r y1 x)
(code1 : L_code (r := r) y1)
(code2 : L_code (r := r) y1)
: (L_recursion_trichotomy_mem (h:=h) y1 code1 y1 code2)
↔  code_mem (L (h:=h) y1) code1 code2
:=
  by
  apply Iff.intro
  · intro hyp
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 h').elim
    | inr hyp =>
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 h').elim
    | inr hyp =>
      cases hyp with
      | intro h' hyp' => exact hyp'
  · intro hyp
    apply Or.inr
    apply Or.inr
    use Eq.refl y1

/-- Stub -/
theorem L_recursion_trichotomy_equiv_first_eq_second
--(x : α)
(y1 : α)
--(h1 : r y1 x)
(code1 : L_code (r := r) y1)
(code2 : L_code (r := r) y1)
: (L_recursion_trichotomy_equiv (h:=h) y1 code1 y1 code2)
↔  code_equiv (L (h:=h) y1) code1 code2
:=
  by
  apply Iff.intro
  · intro hyp
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 h').elim
    | inr hyp =>
    cases hyp with
    | inl hyp =>
      cases hyp with
      | intro h' hyp' => exact (h.wf.irrefl.irrefl y1 h').elim
    | inr hyp =>
      cases hyp with
      | intro h' hyp' => exact hyp'
  · intro hyp
    apply Or.inr
    apply Or.inr
    use Eq.refl y1


/-- Stub -/
theorem L_seg_equiv
  (x : α)
  (c1 c2 : L_code_below x)
: (L (h:=h) x).equiv c1 c2 ↔
  (match c1 with
  | L_code_below.boundcode y1 _ code1 =>
  match c2 with
  | L_code_below.boundcode y2 _ code2 =>
  L_recursion_trichotomy_equiv (h:=h) y1 code1 y2 code2)
:=
  by
  have j
  : L (h:=h) x = L_recursion x (L_hierarchy_below x)
  := L_fixed_point_of_recursion x
  unfold  L_recursion at j
  rw[j]
  dsimp only
  unfold L_recursion_trichotomy_equiv_general
  unfold L_recursion_trichotomy_equiv
  unfold L_hierarchy_below
  rfl


/-- Stub -/
theorem L_seg_mem
  (x : α)
  (c1 c2 : L_code_below x)
: (L (h:=h) x).mem c1 c2 ↔
  (match c1 with
  | L_code_below.boundcode y1 _ code1 =>
  match c2 with
  | L_code_below.boundcode y2 _ code2 =>
  L_recursion_trichotomy_mem (h:=h) y1 code1 y2 code2)
:=
  by
  have j
  : L (h:=h) x = L_recursion x (L_hierarchy_below x)
  := L_fixed_point_of_recursion x
  unfold  L_recursion at j
  rw[j]
  dsimp only
  unfold L_recursion_trichotomy_mem_general
  unfold L_recursion_trichotomy_mem
  unfold L_hierarchy_below
  rfl

/-- Stub -/
theorem L_seg_equiv_of_constructed_boundcodes
  (x : α)
  (y1 : α)
  (h1 : r y1 x)
  (code1 : L_code y1)
  (y2 : α)
  (h2 : r y2 x)
  (code2 : L_code y2)
: (L (h:=h) x).equiv (L_code_below.boundcode y1 h1 code1) (L_code_below.boundcode y2 h2 code2) ↔
  L_recursion_trichotomy_equiv (h:=h) y1 code1 y2 code2
:= by rw [L_seg_equiv]

/-- Stub -/
theorem L_seg_mem_of_upper_constructed_boundcode
  (x : α)
  (c1 : L_code_below x)
  (y2 : α)
  (h2 : r y2 x)
  (code2 : L_code y2)
: (L (h:=h) x).mem c1 (L_code_below.boundcode y2 h2 code2) ↔
  (match c1 with
  | L_code_below.boundcode y1 _ code1 =>
  L_recursion_trichotomy_mem (h:=h) y1 code1 y2 code2)
:= by rw [L_seg_mem]

--We now prove by two facts by simultaneous induction:
--1. That "lift_code" commutes mod equivalence; that is, if y1 < y2 < y3 and `code` is in
--`L_code y1`, then lift_code_{y2,y3} ∘ lift_code_{y1,y2} (code) code_equiv lift_code_{y1,y3}(code).
--2. That if y1 < y3 then `lift_code_{y1,y3}` is an embedding L_{y1+1} → L_{y3+1};
-- that is, given `code1, code2 ∈ L_code y1`, we have `code1 code_equiv code2` iff
-- `lift_code_{y1,y3}(code1) code_equiv lift_code_{y1,y3}(code2)`, and likewise with `code_mem`
-- replacing `code_equiv`.
-- We prove these things by simultaneous induction on the upper bound `y3`.

/-- Stub -/
theorem sats_L_code_param_of_lift_code
  {y2 : α}
  (y1 : α)
  (i : r y1 y2)
  (code : L_code y1)
  (x : L_code_below y2)
: sats_L_code_param (L (h:=h) y2) (lift_code y1 y2 i code) x
↔ (L (h:=h) y2).mem x (L_code_below.boundcode y1 i code)
:=let code_bounded := L_code_below.boundcode y1 i code
  let τ_as_L_List := L_List.cons code_bounded L_List.nil
  let τ := to_List τ_as_L_List
  have hτ
  : σ₅.length = τ.length
  := by rfl
  --now main proof begins
  by
  unfold lift_code
  unfold sats_L_code_param
  dsimp only
  unfold sats
  unfold φ₅
  dsimp only
  let M := LSTModel.mk (L_univ y2) (L (h:=h) y2).equiv (L (h:=h) y2).mem
  have j
  : v₅ ∈ (build_ass
      { univ := L_univ y2, eq := (L (h:=h) y2).equiv, mem := (L (h:=h) y2).mem }
      (LSTF.atomic_mem v₅ v₆) v₅ σ₅ hσ₅
      (to_List (L_List.cons (L_code_below.boundcode y1 i code) L_List.nil)) hτ x).keys
  := eval_build_ass_on_new_var_has_new_var_mem_keys M φ₅ v₅ σ₅ hσ₅ τ hτ x v₅_mem_free_var_φ₅
  have k
  : var_eval
    (build_ass
      { univ := L_univ y2, eq := (L y2).equiv, mem := (L y2).mem }
      (LSTF.atomic_mem v₅ v₆) v₅ σ₅ hσ₅
      (to_List (L_List.cons (L_code_below.boundcode y1 i code) L_List.nil)) hτ x
    ) v₅ j = x
  := eval_build_ass_on_new_var M φ₅ v₅ σ₅ hσ₅ τ hτ x v₅_mem_free_var_φ₅ j
  erw[k]
  have j'
  : v₆ ∈ (build_ass
      { univ := L_univ y2, eq := (L (h:=h) y2).equiv, mem := (L (h:=h) y2).mem }
      (LSTF.atomic_mem v₅ v₆) v₅ σ₅ hσ₅
      (to_List (L_List.cons (L_code_below.boundcode y1 i code) L_List.nil)) hτ x).keys
  := eval_build_ass_has_old_vars_mem_keys M φ₅ v₅ σ₅ hσ₅ τ hτ x v₆ v₆_mem_free_var_φ₅
  have k'
  : var_eval
    (build_ass
      { univ := L_univ y2, eq := (L y2).equiv, mem := (L y2).mem }
      (LSTF.atomic_mem v₅ v₆) v₅ σ₅ hσ₅
      (to_List (L_List.cons (L_code_below.boundcode y1 i code) L_List.nil)) hτ x
    ) v₆ j' = L_code_below.boundcode y1 i code
  :=by
    dsimp
    have eval_var_param_pair_returns
    : eval_var_param_pair σ₅ τ hτ v₆ v₆_mem_σ₅ = L_code_below.boundcode y1 i code
    :=by unfold eval_var_param_pair; rfl
    exact eval_var_param_pair_returns
      ▸ eval_build_ass_on_old_var M φ₅ v₅ v₆ σ₅ hσ₅ τ hτ x v₆_mem_σ₅
  erw[k']

/-- Stub -/
theorem L_seg_mem_of_constructed_boundcodes
  {x : α}
  (y1 : α)
  (h1 : r y1 x)
  (code1 : L_code y1)
  (y2 : α)
  (h2 : r y2 x)
  (code2 : L_code y2)
: (L (h:=h) x).mem (L_code_below.boundcode y1 h1 code1) (L_code_below.boundcode y2 h2 code2) ↔
  L_recursion_trichotomy_mem (h:=h) y1 code1 y2 code2
:= by rw [L_seg_mem]

/-The next few theorems reduce (L x).equiv and (L x).mem statements about
constructed boundcodes (in parameters (y1, jy1, code1) and (y2, jy2, code2) which are the
inputs to the constructors for the boundcodes) to code_equiv and code_mem statements, each
separately in 3 cases depending on the relationship between y1 and y3. Thus, the main point
is it processes the rather trivial trichotomy in each of those cases (where in each case,
2 of the possibilities of the trichotomy are just ruled out directly by the hypotheses).-/

/-- Stub -/
theorem L_seg_equiv_of_constructed_boundcodes_same_level
    {x : α}
    (y : α)
    (jy : r y x)
    (code1 : L_code y)
    (code2 : L_code y)
: (L (h:=h) x).equiv (L_code_below.boundcode y jy code1)
                      (L_code_below.boundcode y jy code2)
↔ code_equiv (L (h:=h) y) code1 code2
:=
  by
  rw[L_seg_equiv]
  dsimp
  unfold L_recursion_trichotomy_equiv
  apply Iff.intro
  · intro hcd
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y h').elim
    | inr hcd =>
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y h').elim
    | inr hcd =>
      cases hcd with
      | intro h' hcd =>
        dsimp at hcd
        exact hcd
  · intro hcd
    apply Or.inr; apply Or.inr
    use (Eq.refl y)

/-- Stub -/
theorem L_seg_mem_of_constructed_boundcodes_same_level
    {x : α}
    (y : α)
    (jy : r y x)
    (code1 : L_code y)
    (code2 : L_code y)
: (L (h:=h) x).mem (L_code_below.boundcode y jy code1)
                      (L_code_below.boundcode y jy code2)
↔ code_mem (L (h:=h) y) code1 code2
:=
  by
  rw[L_seg_mem]
  dsimp
  unfold L_recursion_trichotomy_mem
  apply Iff.intro
  · intro hcd
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y h').elim
    | inr hcd =>
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y h').elim
    | inr hcd =>
      cases hcd with
      | intro h' hcd =>
        dsimp at hcd
        exact hcd
  · intro hcd
    apply Or.inr; apply Or.inr
    use (Eq.refl y)

/-- Stub -/
theorem L_seg_equiv_of_constructed_boundcodes_first_below_second
    {x : α}
    (y1 y2 : α)
    (jy1 : r y1 x)
    (jy2 : r y2 x)
    (jy1y2 : r y1 y2)
    (code1 : L_code y1)
    (code2 : L_code y2)
: (L (h:=h) x).equiv (L_code_below.boundcode y1 jy1 code1)
                      (L_code_below.boundcode y2 jy2 code2)
↔ code_equiv (L (h:=h) y2) (lift_code y1 y2 jy1y2 code1) code2
:=
  by
  rw[L_seg_equiv]
  dsimp
  unfold L_recursion_trichotomy_equiv
  apply Iff.intro
  · intro hcd
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact hcd
    | inr hcd =>
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y1 (IsStrictOrder.toIsTrans.trans y1 y2 y1 jy1y2 h')).elim
    | inr hcd =>
      cases hcd with
      | intro h' hcd =>
        subst h'
        dsimp at hcd
        exact (h.wf.irrefl.irrefl y1 jy1y2).elim
  · intro hcd
    apply Or.inl
    use jy1y2

/-- Stub -/
theorem L_seg_mem_of_constructed_boundcodes_first_below_second
    {x : α}
    (y1 y2 : α)
    (jy1 : r y1 x)
    (jy2 : r y2 x)
    (jy1y2 : r y1 y2)
    (code1 : L_code y1)
    (code2 : L_code y2)
: (L (h:=h) x).mem (L_code_below.boundcode y1 jy1 code1)
                      (L_code_below.boundcode y2 jy2 code2)
↔ code_mem (L (h:=h) y2) (lift_code y1 y2 jy1y2 code1) code2
:=
  by
  rw[L_seg_mem]
  dsimp
  unfold L_recursion_trichotomy_mem
  apply Iff.intro
  · intro hcd
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact hcd
    | inr hcd =>
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y1 (IsStrictOrder.toIsTrans.trans y1 y2 y1 jy1y2 h')).elim
    | inr hcd =>
      cases hcd with
      | intro h' hcd =>
        subst h'
        dsimp at hcd
        exact (h.wf.irrefl.irrefl y1 jy1y2).elim
  · intro hcd
    apply Or.inl
    use jy1y2

/-- Stub -/
theorem L_seg_equiv_of_constructed_boundcodes_second_below_first
    {x : α}
    (y1 y2 : α)
    (jy1 : r y1 x)
    (jy2 : r y2 x)
    (jy1y2 : r y2 y1)
    (code1 : L_code y1)
    (code2 : L_code y2)
: (L (h:=h) x).equiv (L_code_below.boundcode y1 jy1 code1)
                      (L_code_below.boundcode y2 jy2 code2)
↔ code_equiv (L (h:=h) y1) code1 (lift_code y2 y1 jy1y2 code2)
:=
  by
  rw[L_seg_equiv]
  dsimp
  unfold L_recursion_trichotomy_equiv
  apply Iff.intro
  · intro hcd
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y2 (IsStrictOrder.toIsTrans.trans y2 y1 y2 jy1y2 h')).elim
    | inr hcd =>
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact hcd
    | inr hcd =>
      cases hcd with
      | intro h' hcd =>
        subst h'
        dsimp at hcd
        exact (h.wf.irrefl.irrefl y1 jy1y2).elim
  · intro hcd
    apply Or.inr
    apply Or.inl
    use jy1y2

/-- Stub -/
theorem L_seg_mem_of_constructed_boundcodes_second_below_first
    {x : α}
    (y1 y2 : α)
    (jy1 : r y1 x)
    (jy2 : r y2 x)
    (jy1y2 : r y2 y1)
    (code1 : L_code y1)
    (code2 : L_code y2)
: (L (h:=h) x).mem (L_code_below.boundcode y1 jy1 code1)
                      (L_code_below.boundcode y2 jy2 code2)
↔ code_mem (L (h:=h) y1) code1 (lift_code y2 y1 jy1y2 code2)
:=
  by
  rw[L_seg_mem]
  dsimp
  unfold L_recursion_trichotomy_mem
  apply Iff.intro
  · intro hcd
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl y2 (IsStrictOrder.toIsTrans.trans y2 y1 y2 jy1y2 h')).elim
    | inr hcd =>
    cases hcd with
    | inl hcd =>
      cases hcd with
      | intro h' hcd =>
        exact hcd
    | inr hcd =>
      cases hcd with
      | intro h' hcd =>
        subst h'
        dsimp at hcd
        exact (h.wf.irrefl.irrefl y1 jy1y2).elim
  · intro hcd
    apply Or.inr
    apply Or.inl
    use jy1y2

open Lean Meta Elab Tactic

/-- Stub -/
syntax (name := step1_lt_lt_tac) "step1_lt_lt"
  ident ident ident ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step1_lt_lt_tac]
  def eval_step1_lt_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step1_lt_lt $hcd_z $h $yc $yd $z $yc_LT $yd_LT $jz $jc $jd
                            $codec $coded $hcd $lift_codes_with_mem) =>
      evalTactic <| ← `(tactic|
      have $hcd_z : code_mem (L (h := $h) $z) (lift_code $yc $z $jc $codec)
                                              (lift_code $yd $z $jd $coded)
      := $lift_codes_with_mem $yc $yd $z $jz $yc_LT $yd_LT $jc $jd $codec $coded $hcd)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step1_lt_eq_tac) "step1_lt_eq"
  ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step1_lt_eq_tac]
  def eval_step1_lt_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step1_lt_eq $hcd_z $h $yc $z $yc_LT $jz $jc
                            $codec $coded $hcd $lift_first_code_mem_iff) =>
      evalTactic <| ← `(tactic|
      have $hcd_z : code_mem (L (h := $h) $z) (lift_code $yc $z $jc $codec) $coded
      := ($lift_first_code_mem_iff $yc $z $yc_LT $jz $jc $codec $coded).mp $hcd)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step1_eq_lt_tac) (priority := high) "step1_eq_lt"
  ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step1_eq_lt_tac]
  def eval_step1_eq_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step1_eq_lt $hcd_z $h $yd $z $yd_LT $jz $jd
                            $codec $coded $hcd $lift_second_code_mem_iff) =>
      evalTactic <| ← `(tactic|
      have $hcd_z : code_mem (L (h := $h) $z) $codec (lift_code $yd $z $jd $coded)
      := ($lift_second_code_mem_iff $z $yd $jz $yd_LT $jd $codec $coded).mp $hcd)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step1_eq_eq_tac) (priority := high) "step1_eq_eq"
  ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step1_eq_eq_tac]
  def eval_step1_eq_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step1_eq_eq $hcd_z $h $z $jz $codec $coded $hcd) =>
      evalTactic <| ← `(tactic|
      have $hcd_z : code_mem (L (h := $h) $z) $codec $coded
      := (L_seg_mem_of_constructed_boundcodes_same_level $z $jz $codec $coded).mp $hcd)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step2_lt_lt_tac) (priority := 200000) "step2_lt_lt"
  ident ident ident ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step2_lt_lt_tac]
  def eval_step2_lt_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step2_lt_lt $hcc'_z $h $yc $yc' $z $yc_LT $yc'_LT $jz $jc $jc'
                            $codec $codec' $hcc' $lift_codes_with_equiv) =>
      evalTactic <| ← `(tactic|
      have $hcc'_z : code_equiv (L (h := $h) $z) (lift_code $yc $z $jc $codec)
                                                 (lift_code $yc' $z $jc' $codec')
      := $lift_codes_with_equiv $yc $yc' $z $jz $yc_LT $yc'_LT $jc $jc' $codec $codec' $hcc')
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step2_lt_eq_tac) (priority := 200000) "step2_lt_eq"
  ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step2_lt_eq_tac]
  def eval_step2_lt_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step2_lt_eq $hcc'_z $h $yc $z $yc_LT $yc'_LT $jc
                            $codec $codec' $hcc' $lift_first_code_equiv_iff) =>
      evalTactic <| ← `(tactic|
      have $hcc'_z : code_equiv (L (h := $h) $z) (lift_code $yc $z $jc $codec) $codec'
      := ($lift_first_code_equiv_iff $yc $z $yc_LT $yc'_LT $jc $codec $codec').mp $hcc')
    | _ => throwUnsupportedSyntax


/-- Stub -/
syntax (name := step2_eq_lt_tac) (priority := 200000) "step2_eq_lt"
  ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step2_eq_lt_tac]
  def eval_step2_eq_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step2_eq_lt $hcc'_z $h $yc' $z $yc_LT $yc'_LT $jc'
                            $codec $codec' $hcc' $lift_second_code_equiv_iff) =>
      evalTactic <| ← `(tactic|
      have $hcc'_z : code_equiv (L (h := $h) $z) $codec (lift_code $yc' $z $jc' $codec')
      := ($lift_second_code_equiv_iff $z $yc' $yc_LT $yc'_LT $jc' $codec $codec').mp $hcc')
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step2_eq_eq_tac) (priority := 200000) "step2_eq_eq"
  ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step2_eq_eq_tac]
  def eval_step2_eq_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step2_eq_eq $hcc'_z $h $z $jz
                            $codec $codec' $hcc') =>
      evalTactic <| ← `(tactic|
      have $hcc'_z : code_equiv (L (h := $h) $z) $codec $codec'
      := (L_seg_equiv_of_constructed_boundcodes_same_level $z $jz $codec $codec').mp $hcc')
    | _ => throwUnsupportedSyntax


/-- Stub -/
syntax (name := step4_lt_lt_tac) (priority := high) "step4_lt_lt"
  ident ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step4_lt_lt_tac]
  def eval_step4_lt_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step4_lt_lt $hc'd'_z $h $yc' $yd' $z $jc' $jd'
                            $codec' $coded' $hcc'_z $hdd'_z $hcd_z) =>
      evalTactic <| ← `(tactic|
      have $hc'd'_z : code_mem (L (h := $h) $z) (lift_code $yc' $z $jc' $codec')
                                                (lift_code $yd' $z $jd' $coded')
      := code_mem_respects_code_equiv (L $z) $hcc'_z $hdd'_z $hcd_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step4_lt_eq_tac) (priority := high) "step4_lt_eq"
  ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step4_lt_eq_tac]
  def eval_step4_lt_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step4_lt_eq $hc'd'_z $h $yc' $z $jc'
                            $codec' $coded' $hcc'_z $hdd'_z $hcd_z) =>
      evalTactic <| ← `(tactic|
      have $hc'd'_z : code_mem (L (h := $h) $z) (lift_code $yc' $z $jc' $codec') $coded'
      := code_mem_respects_code_equiv (L $z) $hcc'_z $hdd'_z $hcd_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step4_eq_lt_tac) (priority := high) "step4_eq_lt"
  ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step4_eq_lt_tac]
  def eval_step4_eq_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step4_eq_lt $hc'd'_z $h $yd' $z $jd'
                            $codec' $coded' $hcc'_z $hdd'_z $hcd_z) =>
      evalTactic <| ← `(tactic|
      have $hc'd'_z : code_mem (L (h := $h) $z) $codec' (lift_code $yd' $z $jd' $coded')
      := code_mem_respects_code_equiv (L $z) $hcc'_z $hdd'_z $hcd_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step4_eq_eq_tac) (priority := high) "step4_eq_eq"
  ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step4_eq_eq_tac]
  def eval_step4_eq_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step4_eq_eq $hc'd'_z $h $z
                            $codec' $coded' $hcc'_z $hdd'_z $hcd_z) =>
      evalTactic <| ← `(tactic|
      have $hc'd'_z : code_mem (L (h := $h) $z) $codec' $coded'
      := code_mem_respects_code_equiv (L $z) $hcc'_z $hdd'_z $hcd_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step5_lt_lt_tac) (priority := high) "step5_lt_lt"
  ident ident ident ident ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step5_lt_lt_tac]
  def eval_step5_lt_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step5_lt_lt $hc'd'_y3 $h $y3 $yc' $yd' $z $yc'_LT $yd'_LT
                            $jz $jc' $jd' $codec' $coded' $hc'd'_z $lift_codes_mem_iff) =>
      evalTactic <| ← `(tactic|
    have $hc'd'_y3 : (L (h := $h) $y3).mem (L_code_below.boundcode $yc' $yc'_LT $codec')
                                           (L_code_below.boundcode $yd' $yd'_LT $coded')
    := ($lift_codes_mem_iff $yc' $yd' $z $jz $yc'_LT $yd'_LT
        $jc' $jd' $codec' $coded').mpr $hc'd'_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step5_lt_eq_tac) (priority := high) "step5_lt_eq"
  ident ident ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step5_lt_eq_tac]
  def eval_step5_lt_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step5_lt_eq $hc'd'_y3 $h $y3 $yc' $yd' $z $yc'_LT $yd'_LT $jc'
                            $codec' $coded' $hc'd'_z $lift_first_code_mem_iff) =>
      evalTactic <| ← `(tactic|
      have $hc'd'_y3 : (L (h := $h) $y3).mem (L_code_below.boundcode $yc' $yc'_LT $codec')
                                             (L_code_below.boundcode $yd' $yd'_LT $coded')
      := ($lift_first_code_mem_iff $yc' $z $yc'_LT $yd'_LT $jc' $codec' $coded').mpr $hc'd'_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step5_eq_lt_tac) (priority := high) "step5_eq_lt"
  ident ident ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step5_eq_lt_tac]
  def eval_step5_eq_lt : Tactic := fun stx => do
    match stx with
    | `(tactic| step5_eq_lt $hc'd'_y3 $h $y3 $yc' $yd' $z $yc'_LT $yd'_LT $jd'
                            $codec' $coded' $hc'd'_z $lift_second_code_mem_iff) =>
      evalTactic <| ← `(tactic|
      have $hc'd'_y3 : (L (h := $h) $y3).mem (L_code_below.boundcode $yc' $yc'_LT $codec')
                                             (L_code_below.boundcode $yd' $yd'_LT $coded')
      := ($lift_second_code_mem_iff $z $yd' $yc'_LT $yd'_LT $jd' $codec' $coded').mpr $hc'd'_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
syntax (name := step5_eq_eq_tac) (priority := high) "step5_eq_eq"
  ident ident ident ident ident ident ident ident ident ident ident ident : tactic

/-- Stub -/
@[tactic step5_eq_eq_tac]
  def eval_step5_eq_eq : Tactic := fun stx => do
    match stx with
    | `(tactic| step5_eq_eq $hc'd'_y3 $h $y3 $yc' $yd' $z $yc'_LT $yd'_LT $jz
                            $codec' $coded' $hc'd'_z) =>
      evalTactic <| ← `(tactic|
      have $hc'd'_y3 : (L (h := $h) $y3).mem (L_code_below.boundcode $yc' $yc'_LT $codec')
                                             (L_code_below.boundcode $yd' $yd'_LT $coded')
      := (L_seg_mem_of_constructed_boundcodes_same_level $z $jz $codec' $coded').mpr $hc'd'_z)
    | _ => throwUnsupportedSyntax

/-- Stub -/
theorem L_equiv_trans_lemma_all_equal
  {y3 : α}
  (ya : α)
  --(hya : r ya y3)
  (codea : L_code ya)
  (yb : α)
  --(hyb : r yb y3)
  (codeb : L_code yb)
  (yc : α)
  (hyc : r yc y3)
  (codec : L_code yc)
  (hyab : ya = yb)
  (hybc : yb = yc)
  (hyac : ya = yc)
  (equiv_ab : code_equiv (L (h := h) ya) codea (hyab.symm ▸ codeb))
  (equiv_bc : code_equiv (L (h := h) yb) codeb (hybc.symm ▸ codec))
: code_equiv (L (h:=h) ya) codea (hyac ▸ codec)
:=
  by
  subst hyab
  subst hybc
  dsimp
  dsimp at equiv_bc
  dsimp at equiv_ab
  exact (code_equiv_is_Equivalence ya (L (h:=h) ya)).trans equiv_ab equiv_bc

/-- Stub -/
theorem L_equiv_trans_lemma_outers_equal_gt_inner
  {y3 : α}
  (ya : α)
  --(hya : r ya y3)
  (codea : L_code ya)
  (yb : α)
  --(hyb : r yb y3)
  (codeb : L_code yb)
  (yc : α)
  (hyc : r yc y3)
  (codec : L_code yc)
  (hyab : r yb ya)
  (hybc : r yb yc)
  (hyac : ya = yc)
  (equiv_ab : code_equiv (L (h := h) ya) codea (lift_code yb ya hyab codeb))
  (equiv_bc : code_equiv (L (h := h) yc) (lift_code yb yc hybc codeb) codec)
: code_equiv (L (h:=h) ya) codea (hyac ▸ codec)
:=
  by
  subst hyac
  dsimp
  exact (code_equiv_is_Equivalence ya (L (h:=h) ya)).trans equiv_ab equiv_bc

/-- Stub -/
theorem L_equiv_trans_lemma_center_right_equal_gt_left
  {y3 : α}
  (ya : α)
  --(hya : r ya y3)
  (codea : L_code ya)
  (yb : α)
  --(hyb : r yb y3)
  (codeb : L_code yb)
  (yc : α)
  (hyc : r yc y3)
  (codec : L_code yc)
  (hyab : r ya yb)
  (hybc : yb = yc)
  (hyac : r ya yc)
  (equiv_ab : code_equiv (L (h := h) yb) (lift_code ya yb hyab codea) codeb)
  (equiv_bc : code_equiv (L (h := h) yb) codeb (hybc ▸ codec))
: code_equiv (L (h:=h) yb) (lift_code ya yb hyab codea) (hybc ▸ codec)
:=
  by
  subst hybc
  dsimp
  exact (code_equiv_is_Equivalence yb (L (h:=h) yb)).trans equiv_ab equiv_bc

end LL

/-
def next_var (v : var) : var
:=
  match v with
  | var.mk n => var.mk n.succ

 def next_var_2 (v w : var) : var
:= match v with
  | var.mk n =>
    match w with
    | var.mk o => var.mk (max n o).succ

def LSTF.bounded_ex (v w : var) (ψ : LSTF) : LSTF
:= LSTF.ex v (LSTF.conj (LSTF.atomic_mem v w) ψ)

def LSTF.bounded_all (v w : var) (ψ : LSTF) : LSTF
:= LSTF.all v (LSTF.implies (LSTF.atomic_mem v w) ψ)

def LSTF.subset (v w : var) : LSTF
:=
  let z := next_var_2 v w
  LSTF.bounded_all z v (LSTF.atomic_mem z w)

def LSTF.transitive (v : var) : LSTF
:=
  let v' := next_var v
  LSTF.bounded_all v' v (LSTF.subset v' v)

def LSTF.mem_trichotomy (v v' : var) : LSTF
:= LSTF.disj (LSTF.atomic_mem v v') (LSTF.disj (LSTF.atomic_eq v v') (LSTF.atomic_mem v' v))

def LSTF.mem_linear (v : var) : LSTF
:=
  let v' := next_var v
  let v'' := next_var v'
  LSTF.bounded_all v' v (LSTF.bounded_all v'' v (LSTF.mem_trichotomy v' v''))

def LSTF.ordinal (v : var) : LSTF
:= LSTF.conj (LSTF.transitive v) (LSTF.mem_linear v)

def LSTF.mem_upper_bound (v' v : var) : LSTF
:= let z := next_var_2 v' v
  LSTF.bounded_all z v (LSTF.disj (LSTF.atomic_mem z v') (LSTF.atomic_eq z v'))

def LSTF.succ_ordinal (v : var) : LSTF
:= let v' := next_var v
  LSTF.conj (LSTF.ordinal v) (LSTF.bounded_ex v' v (LSTF.mem_upper_bound v' v))

def LSTF.empty (v : var) : LSTF
:= let v' := next_var v
  LSTF.bounded_all v' v (LSTF.neg (LSTF.atomic_mem v' v))

def LSTF.zero_ordinal (v : var) : LSTF
:= LSTF.empty v

def LSTF.zero_or_succ_ordinal (v : var) : LSTF
:= LSTF.disj (LSTF.zero_ordinal v) (LSTF.succ_ordinal v)

def LSTF.every_element_zero_or_succ_ordinal (v : var) : LSTF
:= let z := next_var v
  LSTF.bounded_all z v (LSTF.zero_or_succ_ordinal z)

def LSTF.finite_ordinal (v : var) : LSTF
:= let v' := next_var v
  LSTF.conj (LSTF.zero_or_succ_ordinal v) (LSTF.every_element_zero_or_succ_ordinal v)

def LSTF.not_eq (p q : var)
:= LSTF.neg (LSTF.atomic_eq p q)

def LSTF.not_mem (p q : var)
:= LSTF.neg (LSTF.atomic_mem p q)

def LSTF.first_equals_one_of_two (p q r : var) : LSTF
:= LSTF.disj (LSTF.atomic_eq p q) (LSTF.atomic_eq p r)

def LSTF.both_mem_of_last (p q r : var) : LSTF
:= LSTF.conj (LSTF.atomic_mem p r) (LSTF.atomic_mem q r)

def LSTF.only_possible_members_of_last (p q r : var) : LSTF
:= let z := next_var_2 p (next_var_2 q r)
  LSTF.bounded_all z r (LSTF.first_equals_one_of_two z p q)

def LSTF.last_is_pair_of (p q r : var) : LSTF
:=
  LSTF.conj (LSTF.both_mem_of_last p q r) (LSTF.only_possible_members_of_last p q r)

def LSTF.pair (r : var) : LSTF
:= let p := next_var r
  let q := next_var p
  LSTF.bounded_ex p r (LSTF.bounded_ex q r (LSTF.only_possible_members_of_last p q r))

def LSTF.last_is_ordered_pair_of_first_two_via (p q pp pq r : var) : LSTF
:= LSTF.conj (LSTF.last_is_pair_of pp pq r) (LSTF.conj (LSTF.last_is_pair_of p p pp)
                                                       (LSTF.last_is_pair_of p q pq))

def LSTF.last_is_ordered_pair_of_first_two (p q r : var) : LSTF
:= let pp := next_var_2 p (next_var_2 q r)
  let pq := next_var pp
  LSTF.bounded_ex pp r (LSTF.bounded_ex pq r
                        (LSTF.last_is_ordered_pair_of_first_two_via p q pp pq r))

def LSTF.ordered_pair (r : var): LSTF
:= let p := next_var r
 let q := next_var p
 let spq := next_var q
 LSTF.bounded_ex spq r (LSTF.bounded_ex p spq (LSTF.bounded_ex q spq
                                               (LSTF.last_is_ordered_pair_of_first_two p q r)))

def LSTF.ordered_pair_first_coordinate (p r : var) : LSTF
:= let q := next_var_2 p r
  let spq := next_var q
  LSTF.bounded_ex spq r (LSTF.bounded_ex q spq (LSTF.last_is_ordered_pair_of_first_two p q r))

def LSTF.ordered_pair_second_coordinate (q r : var) : LSTF
:= let p := next_var_2 q r
  let spq := next_var p
  LSTF.bounded_ex spq r (LSTF.bounded_ex p spq (LSTF.last_is_ordered_pair_of_first_two p q r))

def LSTF.set_of_ordered_pairs (f : var) : LSTF
:= let p := next_var f
  LSTF.bounded_all p f (LSTF.ordered_pair p)

def LSTF.if_ordered_pair_then_first_coordinate_in_omega (p : var) : LSTF
:= let qr:= next_var p
  let q:= next_var qr
  LSTF.implies
    (LSTF.ordered_pair p)
    (LSTF.bounded_ex qr p (LSTF.bounded_ex q qr
      (LSTF.conj
        (LSTF.finite_ordinal q)
        (LSTF.ordered_pair_first_coordinate q p))))

def LSTF.ordered_pairs_with_same_output (p p' : var) :  LSTF
:=
  let qr := next_var_2 p p'
  let q := next_var qr
  LSTF.bounded_ex qr p
    (LSTF.bounded_ex q qr
      (LSTF.conj
        (LSTF.ordered_pair_second_coordinate q p)
        (LSTF.ordered_pair_second_coordinate q p')))

def LSTF.function (f : var) : LSTF
:=let p := next_var f
  let p' := next_var p
  let qr := next_var p
  let q := next_var qr
  let r := next_var q
  let qr' := next_var r
  let r' := next_var qr'
  LSTF.bounded_all p f
    (LSTF.bounded_all p' f
      (LSTF.bounded_all qr p
        (LSTF.bounded_all q qr
          (LSTF.bounded_all r qr
            (LSTF.bounded_all qr' p'
              (LSTF.bounded_all r' qr'
                (LSTF.implies
                  (LSTF.conj
                    (LSTF.ordered_pair q r p)
                    (LSTF.ordered_pair q r' p'))
                  (LSTF.atomic_eq r r'))))))))

def LSTF.an_empty_function (f : var) : LSTF
:= let p := next_var f
  LSTF.bounded_all p f
    (LSTF.implies
      (LSTF.ordered_pair p)
      (LSTF.neg (LSTF.atomic_mem p f)))

def LSTF.superset_of_domain (d f : var) : LSTF
:= let p := next_var_2 d f
  let qr := next_var p
  let q := next_var qr
  LSTF.bounded_all p d
    (LSTF.bounded_all qr p
      (LSTF.bounded_all q qr
        (LSTF.implies
          (LSTF.ordered_pair_first_coordinate q p)
          (LSTF.atomic_mem q d))))

def LSTF.subset_of_domain (d f : var) : LSTF
:= let q := next_var_2 d f
  let p := next_var q
  LSTF.bounded_all q d
    (LSTF.bounded_ex p f
      (LSTF.ordered_pair_first_coordinate q p))

def LSTF.is_domain_of (d f : var): LSTF
:=
  LSTF.conj
    (LSTF.subset_of_domain d f)
    (LSTF.superset_of_domain d f)

def LSTF.is_domain_of_the_function (d f : var)
:=
  LSTF.conj
    (LSTF.function f)
    (LSTF.is_domain_of d f)

def LSTF.is_domain_of_the_function_and_is_finite_ordinal
 (d f : var)
:=LSTF.conj
    (LSTF.is_domain_of_the_function d f)
    (LSTF.finite_ordinal d)

def LSTF.formula_family (F : var)
:= LSTF.conj
    (LSTF.set_of_standard_functions_domain_leq_4 F)
    (LSTF.all_outputs_in_omega F)

def LSTF.formula_data (F r : var)
:=
  LSTF.conj
    (LSTF.formula_family F)
    (LSTF.binary_relation F r)

--def L_seg_exists_for_each_ordinal (LSTF.all v₀ (LSTF.implies (formula_ordinal v₀)
        (formula_L_seg_exists v₀)))
--def V_equals_L : LSTF := LSTF.conj (LSTF.all v₀ (L_seg_exists ∨₀)) ()
-/
