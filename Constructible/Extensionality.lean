/-
Copyright (c) 2026 Farmer Schlutzenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Farmer Schlutzenberg, https://sites.google.com/site/schlutzenberg
-/
import Constructible.LHierarchy

set_option linter.unusedVariables false

universe u u'

namespace LL
#check LL.L_code
variable {α : Type u} {r : α → α → Prop} {h : IsWellOrder α r}

theorem lift_first_code_with_equiv
  {y3 : α}
  (yc yd : α)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yc yd)
  (codec : L_code yc)
  (coded : L_code yd)
  (hcd : (L (h := h) y3).equiv (L_code_below.boundcode yc jc codec)
                               (L_code_below.boundcode yd jd coded))
: code_equiv (L (h := h) yd) (lift_code yc yd hc codec) coded
:=
  by
  rw [L_seg_equiv] at hcd
  dsimp at hcd
  unfold L_recursion_trichotomy_equiv at hcd
  cases hcd with
  | inl hcd => --case r yc yd
    cases hcd with
    | intro h' hcd =>
      exact hcd
  | inr hcd =>
  cases hcd with
  | inl hcd => --case r yd yc
    cases hcd with
    | intro h' hcd =>
      --contradiction
      exact (h.wf.irrefl.irrefl yc (IsStrictOrder.toIsTrans.trans yc yd yc hc h')).elim
  | inr hcd => --case yc = yd
    cases hcd with
    | intro h' hcd =>
      --contradiction
      subst h'
      exact (h.wf.irrefl.irrefl yc hc).elim

theorem lift_first_code_mem_iff
  {y3 : α}
  (yc yd : α)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yc yd)
  (codec : L_code yc)
  (coded : L_code yd)
: ((L (h := h) y3).mem (L_code_below.boundcode yc jc codec)
                               (L_code_below.boundcode yd jd coded))
  ↔ (code_mem (L (h := h) yd) (lift_code yc yd hc codec) coded)
:=
  by
  apply Iff.intro
  · intro hcd
    rw [L_seg_mem] at hcd
    dsimp at hcd
    unfold L_recursion_trichotomy_mem at hcd
    cases hcd with
    | inl hcd => --case r yc yd
      cases hcd with
      | intro h' hcd =>
        exact hcd
    | inr hcd =>
    cases hcd with
    | inl hcd => --case r yd yc
      cases hcd with
      | intro h' hcd =>
        --contradiction
        exact (h.wf.irrefl.irrefl yc (IsStrictOrder.toIsTrans.trans yc yd yc hc h')).elim
    | inr hcd => --case yc = yd
      cases hcd with
      | intro h' hcd =>
        --contradiction
        subst h'
        exact (h.wf.irrefl.irrefl yc hc).elim
  · intro hcd
    rw [L_seg_mem]
    dsimp
    unfold L_recursion_trichotomy_mem
    apply Or.inl
    use hc

theorem lift_first_code_equiv_iff
  {y3 : α}
  (yc yd : α)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yc yd)
  (codec : L_code yc)
  (coded : L_code yd)
: ((L (h := h) y3).equiv (L_code_below.boundcode yc jc codec)
                               (L_code_below.boundcode yd jd coded))
  ↔ (code_equiv (L (h := h) yd) (lift_code yc yd hc codec) coded)
:=
  by
  apply Iff.intro
  · intro hcd
    rw [L_seg_equiv] at hcd
    dsimp at hcd
    unfold L_recursion_trichotomy_equiv at hcd
    cases hcd with
    | inl hcd => --case r yc yd
      cases hcd with
      | intro h' hcd =>
        exact hcd
    | inr hcd =>
    cases hcd with
    | inl hcd => --case r yd yc
      cases hcd with
      | intro h' hcd =>
        --contradiction
        exact (h.wf.irrefl.irrefl yc (IsStrictOrder.toIsTrans.trans yc yd yc hc h')).elim
    | inr hcd => --case yc = yd
      cases hcd with
      | intro h' hcd =>
        --contradiction
        subst h'
        exact (h.wf.irrefl.irrefl yc hc).elim
  · intro hcd
    rw [L_seg_equiv]
    dsimp
    unfold L_recursion_trichotomy_equiv
    apply Or.inl
    use hc

theorem lift_second_code_mem_iff
  {y3 : α}
  (yc yd : α)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yd yc)
  (codec : L_code yc)
  (coded : L_code yd)
: ((L (h := h) y3).mem (L_code_below.boundcode yc jc codec)
                               (L_code_below.boundcode yd jd coded))
 ↔ (code_mem (L (h := h) yc) codec (lift_code yd yc hc coded))
:=
  by
  apply Iff.intro
  · intro hcd
    rw [L_seg_mem] at hcd
    dsimp at hcd
    unfold L_recursion_trichotomy_mem at hcd
    cases hcd with
    | inl hcd => --case r yc yd
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl yc (IsStrictOrder.toIsTrans.trans yc yd yc h' hc)).elim
    | inr hcd =>
    cases hcd with
    | inl hcd => --case r yd yc
      cases hcd with
      | intro h' hcd =>
        --contradiction
        exact hcd
    | inr hcd => --case yc = yd
      cases hcd with
      | intro h' hcd =>
        --contradiction
        subst h'
        exact (h.wf.irrefl.irrefl yc hc).elim
  · intro hcd
    rw [L_seg_mem]
    dsimp
    unfold L_recursion_trichotomy_mem
    apply Or.inr
    apply Or.inl
    use hc

theorem lift_second_code_equiv_iff
  {y3 : α}
  (yc yd : α)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yd yc)
  (codec : L_code yc)
  (coded : L_code yd)
: ((L (h := h) y3).equiv (L_code_below.boundcode yc jc codec)
                               (L_code_below.boundcode yd jd coded))
  ↔ (code_equiv (L (h := h) yc) codec (lift_code yd yc hc coded))
:=
  by
  apply Iff.intro
  · intro hcd
    rw [L_seg_equiv] at hcd
    dsimp at hcd
    unfold L_recursion_trichotomy_equiv at hcd
    cases hcd with
    | inl hcd => --case r yc yd
      cases hcd with
      | intro h' hcd =>
        exact (h.wf.irrefl.irrefl yc (IsStrictOrder.toIsTrans.trans yc yd yc h' hc)).elim
    | inr hcd =>
    cases hcd with
    | inl hcd => --case r yd yc
      cases hcd with
      | intro h' hcd =>
        --contradiction
        exact hcd
    | inr hcd => --case yc = yd
      cases hcd with
      | intro h' hcd =>
        --contradiction
        subst h'
        exact (h.wf.irrefl.irrefl yc hc).elim
  · intro hcd
    rw [L_seg_equiv]
    dsimp
    unfold L_recursion_trichotomy_equiv
    apply Or.inr
    apply Or.inl
    use hc


--Induction
--
--The following definitions are the names and statements of the theorems to be
--proved by simultaenous induction on y3. Basically they all assert that certain
--facts hold at y3.

--The first few facts will be proved at level y3 directly from the induction hypothesis,
--without using any of the other facts we will prove at level y3.
def lift_code_commutes {y3 : α} : Prop := ∀
  (y2 y1:α)
  (h23 : r y2 y3)
  (h12: r y1 y2)
  (h13 : r y1 y3)
  (code: L_code y1)
  , code_equiv
      (L (h := h) y3)
      (lift_code y1 y3 h13 code)
      (lift_code y2 y3 h23 (lift_code y1 y2 h12 code))

def lift_codes_with_mem
  {y3 : α} : Prop := ∀
  (yc yd z : α)
  (jz : r z y3)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yc z)
  (hd : r yd z)
  (codec : L_code yc)
  (coded : L_code yd)
  (hcd : (L (h := h) y3).mem (L_code_below.boundcode yc jc codec)
                             (L_code_below.boundcode yd jd coded))
  , code_mem (L (h := h) z) (lift_code yc z hc codec) (lift_code yd z hd coded)

def lift_codes_with_equiv
  {y3 : α} : Prop := ∀
  (yc yd z : α)
  (jz : r z y3)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yc z)
  (hd : r yd z)
  (codec : L_code yc)
  (coded : L_code yd)
  (hcd : (L (h := h) y3).equiv (L_code_below.boundcode yc jc codec)
                               (L_code_below.boundcode yd jd coded))
  , code_equiv (L (h := h) z) (lift_code yc z hc codec) (lift_code yd z hd coded)

def lift_codes_mem_iff
  {y3 : α} : Prop := ∀
  (yc yd z : α)
  (jz : r z y3)
  (jc : r yc y3)
  (jd : r yd y3)
  (hc : r yc z)
  (hd : r yd z)
  (codec : L_code yc)
  (coded : L_code yd)
  , (L (h := h) y3).mem (L_code_below.boundcode yc jc codec)
                               (L_code_below.boundcode yd jd coded)
↔ code_mem (L (h := h) z) (lift_code yc z hc codec) (lift_code yd z hd coded)

def L_seg_equiv_is_Equivalence
    {y3 : α} : Prop :=
    Equivalence (L (h := h) y3).equiv

-- From here on the proofs will use earlier listed results as well as the induction hypothesis
-- (thus, equivalent to just using the induction hypothesis)

/-- This theorem shows that the membership relation for `L y3` respects the equality relation for
`L y3`. Thus, we are given elements `c ≈ c'` and `d ≈ d'` of `L y3`, with `c ∈ d`, and must show
`c' ∈ d'`. The 4 elements are codes of ranks `yc < y3`, `yc' < y3`, `yd < y3`, and `yd' < y3`
respectively. We lift this codes to codes of a common rank `z < y3` and use the theorem
`code_mem_respects_code_equiv` to do the main work. The precise details of the proof depend on 4
things: whether `yc < z` or `yc = z`, whether `yc' < z` or `yc' < yz`, etc. There are 16 possible
combinations of these possibilities, so there are 16 cases in the proof. The proof in each case is
has a similar form: first we make substitutions of those variables of `yc`, `yc'`, `yd` and `yd'`
which equal `z` (replacing them with `z`), and then execute 5 `have` statements, which are each
done using macros defined earlier. Those are as follows: `step1...` converts the assumption `hcd`
into a membership statement at level `z`, the first `step2...` converts the equivalence between `c`,
`c'` at rank max(yc, yc') to one at z, the second `step2...` does likewise for `d`, `d'`, `step4...`
applies `code_mem_respects_code_equiv` at rank `z` to the foregoing things, and then `step5...`
converts the result of that to the desired fact about `L y3`. I did try to make the proof uniform in
cases, but had trouble in connection with type errors coming from the variables `yc` etc collapsing
to `z`. -/
def L_seg_mem_respects_equiv
  {y3 : α} : Prop := ∀
  (c c' d d' : L_univ y3)
  (hcc' : (L (h := h) y3).equiv c c')
  (hdd' : (L (h := h) y3).equiv d d')
  (hcd : (L (h := h) y3).mem c d)
  , (L (h := h) y3).mem c' d'

/-- One quarter of extensionality. Note that it only does → in the implication between the
membership statements. -/
def L_extensional_equiv_implies_mp
  {y3 : α} : Prop := ∀
  (d d' : L_univ y3)
  , (L (h := h) y3).equiv d d'
    → ∀ (x : L_univ y3), ((L (h := h) y3).mem x d → (L (h := h) y3).mem x d')

/-- One half of extensionality. It has the ↔ between the membership statements. -/
def L_extensional_equiv_implies
  {y3 : α} : Prop := ∀
  (d d' : L_univ y3)
  , (L (h := h) y3).equiv d d'
    → ∀ (x : L_univ y3), ((L (h := h) y3).mem x d ↔ (L (h := h) y3).mem x d')

def code_equiv_iff
  {y3 : α} : Prop := ∀
  (y:α)
  (_ : r y y3)
  (c c' : L_code y),
  (code_equiv (L (h := h) y) c c')
  ↔ ∀ (x:α) (jx : r x y) (codex : L_code x),
        (  code_mem (L (h := h) y) (lift_code x y jx codex) c
         ↔ code_mem (L (h := h) y) (lift_code x y jx codex) c')

def L_extensional_mem_implies
  {y3 : α} : Prop
:= ∀ (d d' : L_univ y3),
    (∀ (c : L_univ y3),
      ((L (h := h) y3).mem c d ↔ (L (h := h) y3).mem c d')) → (L (h := h) y3).equiv d d'

def L_extensional
  {y3 : α} : Prop
:= ∀ (d d' : L_univ (r := r) y3),
      ((L (r := r) (h := h) y3).equiv d d')
      ↔ (∀ (x : L_univ (r := r) y3),
          (((L (r := r) (h := h) y3).mem x d) ↔ ((L (r := r) (h := h) y3).mem x d')))

def lift_code_equiv_emb {y3 : α} : Prop := ∀
  {y1:α}
  (h13 : r y1 y3)
  (code1 code2 : L_code (r:=r) y1),
    (code_equiv (L (h := h) y1) code1 code2)
    ↔ (code_equiv (L (h := h) y3)
      (lift_code y1 y3 h13 code1)
      (lift_code y1 y3 h13 code2))

def L_equiv_trans_lemma_outers_equal_lt_inner
    {y3 : α}
: Prop
:=  ∀ (ya : α)
    (hya : r ya y3)
    (codea : L_code ya)
    (yb : α)
    (hyb : yb = y3)
    (codeb : L_code yb)
    (yc : α)
    (hyc : r yc y3)
    (codec : L_code yc)
    (hyab : r ya yb)
    (hybc : r yc yb)
    (hyac : ya = yc)
    (equiv_ab : code_equiv (L (h := h) yb) (lift_code ya yb hyab codea) codeb)
    (equiv_bc : code_equiv (L (h := h) yb) codeb (lift_code yc yb hybc codec))
  , code_equiv (L (h := h) ya) codea (hyac ▸ codec)

def L_equiv_trans_lemma_center_right_equal_lt_left
    {y3 : α} : Prop :=
  ∀ (ya : α)
    (hya : ya = y3)
    (codea : L_code ya)
    (yb : α)
    (hyb : r yb y3)
    (codeb : L_code yb)
    (yc : α)
    (hyc : r yc y3)
    (codec : L_code yc)
    (hyab : r yb ya)
    (hybc : yb = yc)
    (hyac : r yc ya)
    (equiv_ab : code_equiv (L (h := h) ya) codea (lift_code yb ya hyab codeb))
    (equiv_bc : code_equiv (L (h := h) yb) codeb (hybc ▸ codec))
  , code_equiv (L (h := h) ya) codea (lift_code yc ya hyac codec)

def L_equiv_trans_lemma_center_lt_left_lt_right
    {y3 : α} : Prop :=
  ∀ (ya : α)
    (hya : r ya y3)
    (codea : L_code ya)
    (yb : α)
    (hyb : r yb y3)
    (codeb : L_code yb)
    (yc : α)
    (hyc : yc = y3)
    (codec : L_code yc)
    (hyab : r yb ya)
    (hybc : r yb yc)
    (hyac : r ya yc)
    (equiv_ab : code_equiv (L (h := h) ya) codea (lift_code yb ya hyab codeb))
    (equiv_bc : code_equiv (L (h := h) yc) (lift_code yb yc hybc codeb) codec)
  , code_equiv (L (h := h) yc) (lift_code ya yc hyac codea) codec

def L_equiv_trans_lemma_left_lt_center_lt_right
    {y3 : α} : Prop :=
  ∀ (ya : α)
    (hya : r ya y3)
    (codea : L_code ya)
    (yb : α)
    (hyb : r yb y3)
    (codeb : L_code yb)
    (yc : α)
    (hyc : yc = y3)
    (codec : L_code yc)
    (hyab : r ya yb)
    (hybc : r yb yc)
    (hyac : r ya yc)
    (equiv_ab : code_equiv (L (h := h) yb) (lift_code ya yb hyab codea) codeb)
    (equiv_bc : code_equiv (L (h := h) yc) (lift_code yb yc hybc codeb) codec)
  , code_equiv (L (h := h) yc) (lift_code ya yc hyac codea) codec

def L_equiv_trans_lemma_left_lt_right_lt_center
    {y3 : α} : Prop :=
  ∀ (ya : α)
    (hya : r ya y3)
    (codea : L_code ya)
    (yb : α)
    (hyb : yb = y3)
    (codeb : L_code yb)
    (yc : α)
    (hyc : r yc y3)
    (codec : L_code yc)
    (hyab : r ya yb)
    (hybc : r yc yb)
    (hyac : r ya yc)
    (equiv_ab : code_equiv (L (h := h) yb) (lift_code ya yb hyab codea) codeb)
    (equiv_bc : code_equiv (L (h := h) yb) codeb (lift_code yc yb hybc codec))
  , code_equiv (L (h := h) yc) (lift_code ya yc hyac codea) codec

def sats_L_code_param_respects_equiv_param
  {y3 : α} : Prop := ∀
  (c : L_code (r:=r) y3)
  {p q : L_univ (r:=r) y3}
  (hpq : (L (r:=r) (h := h) y3).equiv p q)
  (hsats : sats_L_code_param (L (r:=r) (h := h) y3) c p)
  , sats_L_code_param (L (r:=r) (h := h) y3) c q

def lift_code_mem_emb {y3 : α} : Prop := ∀
  (y1:α)
  (h13 : r y1 y3)
  (code1 code2 : L_code (r:=r) y1)
  , (code_mem (L (h := h) y1) code1 code2)
    ↔ (code_mem (L (h := h) y3)
      (lift_code y1 y3 h13 code1)
      (lift_code y1 y3 h13 code2))

--Our inductive hypothesis at y3 is that the assertions stated above hold at all y < y3 (that is,
--with the parameter y3 above replaced by y).

structure L_ext_inductive_properties (y : α) : Prop  where
  L_equiv_trans_lemma_outers_equal_lt_inner :
    L_equiv_trans_lemma_outers_equal_lt_inner (y3 := y) (h := h)
  L_equiv_trans_lemma_center_right_equal_lt_left :
    L_equiv_trans_lemma_center_right_equal_lt_left (y3 := y) (h := h)
  L_equiv_trans_lemma_center_lt_left_lt_right :
    L_equiv_trans_lemma_center_lt_left_lt_right (y3 := y) (h := h)
  L_equiv_trans_lemma_left_lt_center_lt_right :
    L_equiv_trans_lemma_left_lt_center_lt_right (y3 := y) (h := h)
  L_equiv_trans_lemma_left_lt_right_lt_center :
     L_equiv_trans_lemma_left_lt_right_lt_center (y3 := y) (h := h)
  L_seg_equiv_is_Equivalence : L_seg_equiv_is_Equivalence (y3 := y) (h := h)
  lift_codes_with_mem : lift_codes_with_mem (y3 := y) (h := h)
  lift_codes_with_equiv : lift_codes_with_equiv (y3 := y) (h := h)
  lift_codes_mem_iff : lift_codes_mem_iff (y3 := y) (h := h)
  L_seg_mem_respects_equiv : L_seg_mem_respects_equiv (y3 := y) (h := h)
  L_extensional_equiv_implies_mp : L_extensional_equiv_implies_mp (y3 := y) (h := h)
  L_extensional_equiv_implies : L_extensional_equiv_implies (y3 := y) (h := h)
  code_equiv_iff : code_equiv_iff (y3 := y) (h := h)
  L_extensional_mem_implies : L_extensional_mem_implies (y3 := y) (h := h)
  L_extensional : L_extensional (y3 := y) (h := h)
  sats_L_code_param_respects_equiv_param : sats_L_code_param_respects_equiv_param (y3 := y) (h := h)
  lift_code_commutes : lift_code_commutes (y3 := y) (h := h)
  lift_code_equiv_emb : lift_code_equiv_emb (y3 := y) (h := h)
  lift_code_mem_emb : lift_code_mem_emb (y3 := y) (h := h)

def ext_IH (y : α) : Prop :=
  ∀ {z : α} (rankhyp : r z y), L_ext_inductive_properties z (h:=h)

--
--Proofs begin
theorem ind_lift_code_commutes
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: lift_code_commutes (y3 := y3) (h := h)
:=
    by
    unfold lift_code_commutes
    intro y2 y1 h23 h12 h13 code
    unfold code_equiv
    intro x
    rw [sats_L_code_param_of_lift_code]
    rw [sats_L_code_param_of_lift_code]
    rw [L_seg_mem_of_upper_constructed_boundcode]
    rw [L_seg_mem_of_upper_constructed_boundcode]
    cases x with
    | boundcode yx hx codex =>
      dsimp
      apply Iff.intro
      · unfold L_recursion_trichotomy_mem
        intro hyp
        cases hyp with
        | inl hyp => --case yx < y1
          cases hyp with
          | intro h' hyp =>
          apply Or.inl
          use (Trans.trans h' h12)
          have lift_hyp
          : code_mem (L y2) (lift_code y1 y2 h12 (lift_code yx y1 h' codex))
              (lift_code y1 y2 h12 code)
          := ((ihyp h23).lift_code_mem_emb y1 h12 (lift_code yx y1 h' codex) code).mp hyp
          have lifts_equiv
          : code_equiv (L (h := h) y2)
              (lift_code yx y2 (Trans.trans h' h12) codex)
              (lift_code y1 y2 h12 (lift_code yx y1 h' codex))
          := ((ihyp h23).lift_code_commutes y1 yx h12 h' (Trans.trans h' h12) codex)
          have lifted_y1_equiv_self
          : code_equiv
            (L (h := h) y2)
            (lift_code y1 y2 h12 code)
            (lift_code y1 y2 h12 code)
          := ((code_equiv_is_Equivalence y2 (L (h := h) y2)).refl (lift_code y1 y2 h12 code))
          exact code_mem_respects_code_equiv (L (h := h) y2)
                  ((code_equiv_is_Equivalence y2 (L (h := h) y2)).symm lifts_equiv)
                  lifted_y1_equiv_self
                  lift_hyp
        | inr hyp =>
        cases hyp with
        | inl hyp => -- case y1 < yx
          cases hyp with
          | intro h' hyp =>
            cases h.toTrichotomous.rel_or_eq_or_rel_swap (a:=yx) (b:=y2) with
            | inl hyxy2 =>
              apply Or.inl
              use hyxy2
              have lifts_equiv :
              code_equiv
                (L (h := h) y2)
                (lift_code y1 y2 h12 code)
                (lift_code yx y2 hyxy2 (lift_code y1 yx h' code))
              := ((ihyp h23).lift_code_commutes yx y1 hyxy2 h' (Trans.trans h' hyxy2) code)
              have lift_hyp
              : code_mem (L y2) (lift_code yx y2 hyxy2 codex)
                  (lift_code yx y2 hyxy2 (lift_code y1 yx h' code))
              := ((ihyp h23).lift_code_mem_emb yx hyxy2 codex (lift_code y1 yx h' code)).mp hyp
              exact code_mem_respects_code_equiv (L (h := h) y2)
                ((code_equiv_is_Equivalence y2 (L (h := h) y2)).refl (lift_code yx y2 hyxy2 codex))
                ((code_equiv_is_Equivalence y2 (L (h := h) y2)).symm lifts_equiv)
                  lift_hyp
            | inr hyxy2 =>
            cases hyxy2 with
            | inl hyxy2 =>
              apply Or.inr
              apply Or.inr
              use hyxy2
              have hy2yx : y2 = yx := hyxy2.symm
              subst hy2yx
              exact hyp
            | inr hyxy2 =>
              apply Or.inr
              apply Or.inl
              use hyxy2
              have lifts_equiv
              :
                code_equiv
                  (L (h := h) yx)
                  (lift_code y1 yx h' code)
                  (lift_code y2 yx hyxy2 (lift_code y1 y2 h12 code))
                := ((ihyp hx).lift_code_commutes y2 y1 hyxy2 h12 (Trans.trans h12 hyxy2) code)
              exact code_mem_respects_code_equiv (L (h := h) yx)
                  ((code_equiv_is_Equivalence yx (L (h := h) yx)).refl codex)
                  lifts_equiv
                  hyp
        | inr hyp => -- case yx = y1
          cases hyp with
          | intro h' hyp =>
            have h'' : y1 = yx := h'.symm
            subst h''
            apply Or.inl
            use h12
            dsimp only at hyp
            exact ((ihyp h23).lift_code_mem_emb y1 h12 codex code).mp hyp
      · intro hyp
        cases h.toTrichotomous.rel_or_eq_or_rel_swap (a:=yx) (b:=y1) with
        | inl hx1 => --case yx < y1
          apply Or.inl
          use hx1
          have hyp_case
          : code_mem (L y2) (lift_code yx y2 (IsStrictOrder.toIsTrans.trans yx y1 y2 hx1 h12) codex)
              (lift_code y1 y2 h12 code)
          :=  (L_recursion_trichotomy_mem_first_lt_second
                y3 yx hx codex y2 h23 (lift_code y1 y2 h12 code)
                (IsStrictOrder.toIsTrans.trans yx y1 y2 hx1 h12)
              ).mp hyp
          have lifts_equiv
          : code_equiv
              (L (h := h) y2)
              (lift_code yx y2 (IsStrictOrder.toIsTrans.trans yx y1 y2 hx1 h12) codex)
              (lift_code y1 y2 h12 (lift_code yx y1 hx1 codex))
            :=  ((ihyp h23).lift_code_commutes y1 yx h12 hx1
                (IsStrictOrder.toIsTrans.trans yx y1 y2 hx1 h12) codex)
          have hyp_case_equiv
          : code_mem (L y2) (lift_code y1 y2 h12 (lift_code yx y1 hx1 codex))
              (lift_code y1 y2 h12 code)
          :=  code_mem_respects_code_equiv (L y2) lifts_equiv
                ((code_equiv_is_Equivalence y2 (L y2)).refl (lift_code y1 y2 h12 code)) hyp_case
          exact   ((ihyp h23).lift_code_mem_emb y1 h12 (lift_code yx y1 hx1 codex) code).mpr
                   hyp_case_equiv
        | inr hx1 =>
        cases hx1 with
        | inl hx1 => --Case yx = y1
          apply Or.inr
          apply Or.inr
          subst hx1
          dsimp
          use (Eq.refl yx)
          have hyp_case : code_mem (L y2) (lift_code yx y2 h12 codex) (lift_code yx y2 h12 code)
          :=
            (L_recursion_trichotomy_mem_first_lt_second y3 yx hx codex y2 h23
              (lift_code yx y2 h12 code) h12).mp hyp
          exact ((ihyp h23).lift_code_mem_emb yx h12 codex code).mpr hyp_case
        | inr hx1 => --Case y1 < yx
          apply Or.inr
          apply Or.inl
          use hx1
          cases hyp with
          | inl hyp => -- Case y1 < yx < y2
            cases hyp with
            | intro h' hyp' =>
              have lifts_equiv
              :
                code_equiv
                  (L (h := h) y2)
                  (lift_code y1 y2 (IsStrictOrder.toIsTrans.trans y1 yx y2 hx1 h') code)
                  (lift_code yx y2 h' (lift_code y1 yx hx1 code))
              :=  ((ihyp h23).lift_code_commutes yx y1 h' hx1
                  (IsStrictOrder.toIsTrans.trans y1 yx y2 hx1 h') code)
              have hyp_case_equiv
              : code_mem (L y2) (lift_code yx y2 h' codex)
                  (lift_code yx y2 h' (lift_code y1 yx hx1 code))
              :=
                code_mem_respects_code_equiv (L y2)
                  ((code_equiv_is_Equivalence y2 (L y2)).refl (lift_code yx y2 h' codex))
                  lifts_equiv hyp'
              exact ((ihyp h23).lift_code_mem_emb yx h' codex (lift_code y1 yx hx1 code)).mpr
                      hyp_case_equiv
          | inr hyp =>
          cases hyp with
          | inl hyp => --Case y1 < y2 < yx
            cases hyp with
            | intro h' hyp' =>
              have lifts_equiv
              :
                code_equiv
                  (L (h := h) yx)
                  (lift_code y1 yx (IsStrictOrder.toIsTrans.trans y1 y2 yx h12 h') code)
                  (lift_code y2 yx h' (lift_code y1 y2 h12 code))
              :=  ((ihyp hx).lift_code_commutes y2 y1 h' h12 hx1 code)
              exact code_mem_respects_code_equiv (L yx)
                      ((code_equiv_is_Equivalence yx (L yx)).refl codex)
                      ((code_equiv_is_Equivalence yx (L yx)).symm lifts_equiv)
                      hyp'
          | inr hyp => -- Case y1 < y2 = yx
            cases hyp with
            | intro h' hyp' =>
              subst h'
              dsimp at hyp'
              exact hyp'

theorem ind_lift_codes_with_mem
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: lift_codes_with_mem (y3 := y3) (h := h)
:=
  by
  unfold lift_codes_with_mem
  intro yc yd z jz jc jd hc hd codec coded hcd
  rw [L_seg_mem] at hcd
  dsimp at hcd
  unfold L_recursion_trichotomy_mem at hcd
  cases hcd with
  | inl hcd => --case r yc yd
    cases hcd with
    | intro h' hcd =>
      have hcd_z :  code_mem (L z) (lift_code yd z hd (lift_code yc yd h' codec))
                      (lift_code yd z hd coded)
      := ((ihyp jz).lift_code_mem_emb yd hd (lift_code yc yd h' codec) coded).mp hcd
      have lift_codes_equivalent :  code_equiv (L z) (lift_code yc z hc codec)
                                      (lift_code yd z hd (lift_code yc yd h' codec))
      := ((ihyp jz).lift_code_commutes yd yc hd h' hc codec)
      exact code_mem_respects_code_equiv
        (L z)
        ((code_equiv_is_Equivalence z (L z)).symm lift_codes_equivalent)
        ((code_equiv_is_Equivalence z (L z)).refl (lift_code yd z hd coded))
        hcd_z
  | inr hcd =>
  cases hcd with
  | inl hcd => --case r yd yc
    cases hcd with
    | intro h' hcd =>
      have hcd_z :  code_mem (L z) (lift_code yc z hc codec)
                      (lift_code yc z hc (lift_code yd yc h' coded))
      := ((ihyp jz).lift_code_mem_emb yc hc codec (lift_code yd yc h' coded)).mp hcd
      have lift_codes_equivalent :  code_equiv (L z) (lift_code yd z hd coded)
                                      (lift_code yc z hc (lift_code yd yc h' coded))
      := ((ihyp jz).lift_code_commutes yc yd hc h' hd coded)
      exact code_mem_respects_code_equiv
        (L z)
        ((code_equiv_is_Equivalence z (L z)).refl (lift_code yc z hc codec))
        ((code_equiv_is_Equivalence z (L z)).symm lift_codes_equivalent)
        hcd_z
  | inr hcd => --case yc = yd
    cases hcd with
    | intro h' hcd =>
      subst h'
      dsimp at hcd
      exact ((ihyp jz).lift_code_mem_emb yc hc codec coded).mp hcd

theorem ind_lift_codes_with_equiv
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: lift_codes_with_equiv (y3 := y3) (h := h)
:=
  by
  unfold lift_codes_with_equiv
  intro yc yd z jz jc jd hc hd codec coded hcd
  rw [L_seg_equiv] at hcd
  dsimp at hcd
  unfold L_recursion_trichotomy_equiv at hcd
  cases hcd with
  | inl hcd => --case r yc yd
    cases hcd with
    | intro h' hcd =>
      have hcd_z : code_equiv (L z)
                     (lift_code yd z hd (lift_code yc yd h' codec)) (lift_code yd z hd coded)
      := ((ihyp jz).lift_code_equiv_emb hd (lift_code yc yd h' codec) coded).mp hcd
      have lift_codes_equivalent :  code_equiv (L z) (lift_code yc z hc codec)
                                      (lift_code yd z hd (lift_code yc yd h' codec))
      := ((ihyp jz).lift_code_commutes yd yc hd h' hc codec)
      exact (code_equiv_is_Equivalence z (L z)).trans lift_codes_equivalent hcd_z
  | inr hcd =>
  cases hcd with
  | inl hcd => --case r yd yc
    cases hcd with
    | intro h' hcd =>
      have hcd_z :  code_equiv (L z) (lift_code yc z hc codec)
                      (lift_code yc z hc (lift_code yd yc h' coded))
      := ((ihyp jz).lift_code_equiv_emb hc codec (lift_code yd yc h' coded)).mp hcd
      have lift_codes_equivalent :  code_equiv (L z) (lift_code yd z hd coded)
                                      (lift_code yc z hc (lift_code yd yc h' coded))
      := (ihyp jz).lift_code_commutes yc yd hc h' hd coded
      exact (code_equiv_is_Equivalence z (L z)).symm
              ((code_equiv_is_Equivalence z (L z)).trans
                lift_codes_equivalent
                ((code_equiv_is_Equivalence z (L z)).symm hcd_z))
  | inr hcd => --case yc = yd
    cases hcd with
    | intro h' hcd =>
      subst h'
      dsimp at hcd
      exact ((ihyp jz).lift_code_equiv_emb hc codec coded).mp hcd

theorem ind_lift_codes_mem_iff
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: lift_codes_mem_iff (y3 := y3) (h := h)
:=
  by
  unfold lift_codes_mem_iff
  intro yc yd z jz jc jd hc hd codec coded
  apply Iff.intro
  · intro hcd
    rw [L_seg_mem] at hcd
    dsimp at hcd
    unfold L_recursion_trichotomy_mem at hcd
    cases hcd with
    | inl hcd => --case r yc yd
      cases hcd with
      | intro h' hcd =>
        have hcd_z :  code_mem (L z) (lift_code yd z hd (lift_code yc yd h' codec))
                        (lift_code yd z hd coded)
        := ((ihyp jz).lift_code_mem_emb yd hd (lift_code yc yd h' codec) coded).mp hcd
        have lift_codes_equiv : code_equiv (L z) (lift_code yc z hc codec)
                                  (lift_code yd z hd (lift_code yc yd h' codec))
        := (ihyp jz).lift_code_commutes yd yc hd h' hc codec
        exact
          (code_mem_respects_code_equiv_iff
            (L z)
            lift_codes_equiv
            ((code_equiv_is_Equivalence z (L z)).refl (lift_code yd z hd coded))).mpr hcd_z
    | inr hcd =>
    cases hcd with
    | inl hcd => --case r yd yc
      cases hcd with
      | intro h' hcd =>
        have hcd_z :  code_mem (L z) (lift_code yc z hc codec)
                        (lift_code yc z hc (lift_code yd yc h' coded))
        := ((ihyp jz).lift_code_mem_emb yc hc codec (lift_code yd yc h' coded)).mp hcd
        have lift_codes_equiv : code_equiv (L z) (lift_code yd z hd coded)
                                  (lift_code yc z hc (lift_code yd yc h' coded))
        := (ihyp jz).lift_code_commutes yc yd hc h' hd coded
        exact
          (code_mem_respects_code_equiv_iff
            (L z)
            ((code_equiv_is_Equivalence z (L z)).refl (lift_code yc z hc codec))
            lift_codes_equiv).mpr hcd_z
    | inr hcd => --case yc = yd
      cases hcd with
      | intro h' hcd =>
        subst h'
        dsimp at hcd
        exact ((ihyp jz).lift_code_mem_emb yc hc codec coded).mp hcd
  · intro hcd
    rw [L_seg_mem]
    dsimp
    unfold L_recursion_trichotomy_mem
    cases h.toTrichotomous.rel_or_eq_or_rel_swap  (a:=yc) (b:=yd) with
    | inl jcd =>
      apply Or.inl
      use jcd
      have lift_codes_equiv : code_equiv (L z) (lift_code yc z hc codec)
                                (lift_code yd z hd (lift_code yc yd jcd codec))
      := (ihyp jz).lift_code_commutes yd yc hd jcd hc codec
      have : code_mem (L z) (lift_code yd z hd (lift_code yc yd jcd codec))
              (lift_code yd z hd coded)
      :=  (code_mem_respects_code_equiv_iff (L z) lift_codes_equiv
            ((code_equiv_is_Equivalence z (L z)).refl (lift_code yd z hd coded))).mp hcd
      exact ((ihyp jz).lift_code_mem_emb yd hd (lift_code yc yd jcd codec) coded).mpr this
    | inr jcd =>
    cases jcd with
    | inl jcd =>
      apply Or.inr
      apply Or.inr
      subst jcd
      use (Eq.refl yc)
      dsimp
      exact ((ihyp jz).lift_code_mem_emb yc hc codec coded).mpr hcd
    | inr jcd =>
      apply Or.inr
      apply Or.inl
      use jcd
      have lift_codes_equiv : code_equiv (L z) (lift_code yd z hd coded)
                                (lift_code yc z hc (lift_code yd yc jcd coded))
      := (ihyp jz).lift_code_commutes yc yd hc jcd hd coded
      have :  code_mem (L z) (lift_code yc z hc codec)
                (lift_code yc z hc (lift_code yd yc jcd coded))
      :=  (code_mem_respects_code_equiv_iff (L z)
            ((code_equiv_is_Equivalence z (L z)).refl (lift_code yc z hc codec))
              lift_codes_equiv
          ).mp hcd
      exact ((ihyp jz).lift_code_mem_emb yc hc codec (lift_code yd yc jcd coded)).mpr this

theorem ind_L_seg_equiv_is_Equivalence
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_seg_equiv_is_Equivalence (y3 := y3) (h := h)
:=
{
      refl (a : L_univ (r:=r) y3)
      :=
        by
        match a with
        | L_code_below.boundcode ya hya codea =>
          rw [L_seg_equiv_of_constructed_boundcodes]
          unfold L_recursion_trichotomy_equiv
          apply Or.inr
          apply Or.inr
          use (Eq.refl ya)
          dsimp
          exact (code_equiv_is_Equivalence ya (L (h := h) ya)).refl codea

      symm
        {a b : L_univ y3}
        (hypab : (L (h := h) y3).equiv a b)
      :=
        by
        match a, b with
        | L_code_below.boundcode ya hya codea, L_code_below.boundcode yb hyb codeb =>
        rw [L_seg_equiv_of_constructed_boundcodes]
        rw [L_seg_equiv_of_constructed_boundcodes] at hypab
        unfold L_recursion_trichotomy_equiv
        unfold L_recursion_trichotomy_equiv at hypab
        cases hypab with
        | inl hypab => --Case ya < yb
          cases hypab with
          | intro h' hypab =>
            apply Or.inr
            apply Or.inl
            use h'
            exact (code_equiv_is_Equivalence yb (L (h := h) yb)).symm hypab
        | inr hypab =>
          cases hypab with
          | inl hypab => -- Case yb < ya
            cases hypab with
            | intro h' hypab =>
            apply Or.inl
            use h'
            exact (code_equiv_is_Equivalence ya (L (h := h) ya)).symm hypab
          | inr hypab => -- Case ya = yb
            cases hypab with
            | intro h' hypab =>
            apply Or.inr
            apply Or.inr
            use h'.symm
            subst h'
            dsimp
            dsimp at hypab
            exact (code_equiv_is_Equivalence ya (L (h := h) ya)).symm hypab

      trans
        {a b c : L_univ y3}
        (hypab : (L (h := h) y3).equiv a b)
        (hypbc : (L (h := h) y3).equiv b c)
      :=
        by
        match a, b, c with
        | L_code_below.boundcode ya hya codea,
          L_code_below.boundcode yb hyb codeb,
          L_code_below.boundcode yc hyc codec =>
        rw [L_seg_equiv_of_constructed_boundcodes]
        rw [L_seg_equiv_of_constructed_boundcodes] at hypab
        rw [L_seg_equiv_of_constructed_boundcodes] at hypbc
        unfold L_recursion_trichotomy_equiv
        cases hypab with
        | inl hypab =>
          -- Case 1: ya < yb
          cases hypab with
          | intro h' hypab =>
            cases hypbc with
            | inl hypbc =>
              -- Subcase 1.1: ya < yb < yc
              cases hypbc with
              | intro h'' hypbc =>
                apply Or.inl
                let h''' := IsStrictOrder.toIsTrans.trans ya yb yc h' h''
                use h'''
                exact (ihyp hyc).L_equiv_trans_lemma_left_lt_center_lt_right
                        ya h''' codea yb h'' codeb yc (Eq.refl yc) codec h' h'' h''' hypab hypbc
            | inr hypbc =>
              cases hypbc with
              | inl hypbc => -- Subcase 1.2: ya < yb ∧ yc < yb
                cases hypbc with
                | intro h'' hypbc =>
                cases trichotomous (r := r) ya yc with
                | inl hyac => -- ya < yc < yb
                  apply Or.inl
                  use hyac
                  exact (ihyp hyb).L_equiv_trans_lemma_left_lt_right_lt_center
                          ya h' codea yb (Eq.refl yb) codeb yc h'' codec h' h'' hyac hypab hypbc
                | inr hyac =>
                  cases hyac with
                  | inl hyac => --ya = yc < yb
                    apply Or.inr
                    apply Or.inr
                    use hyac
                    subst hyac
                    dsimp
                    exact (ihyp hyb).L_equiv_trans_lemma_outers_equal_lt_inner
                      ya h' codea yb (Eq.refl yb) codeb ya h'' codec h' h'' (Eq.refl ya) hypab hypbc
                  | inr hyac => --yc < ya < yb
                    apply Or.inr
                    apply Or.inl
                    use hyac
                    exact
                      (code_equiv_is_Equivalence ya (L (h := h) ya)).symm
                        ((ihyp hyb).L_equiv_trans_lemma_left_lt_right_lt_center
                          yc h'' codec yb (Eq.refl yb) codeb ya h' codea h'' h' hyac
                          ((code_equiv_is_Equivalence yb (L (h := h) yb)).symm hypbc)
                          ((code_equiv_is_Equivalence yb (L (h := h) yb)).symm hypab))
              | inr hypbc =>
                -- Subcase 1.3: ya < yb = yc
                cases hypbc with
                | intro h'' hypbc =>
                  subst h''
                  dsimp at hypbc
                  apply Or.inl
                  use h'
                  exact L_equiv_trans_lemma_center_right_equal_gt_left
                          ya hya codea yb hyb codeb yb hyb codec h' (Eq.refl yb) h' hypab hypbc
        | inr  hypab =>
          cases hypab with
          | inl hypab =>
            --Case 2 : yb < ya
            cases hypab with
            | intro h' hypab =>
              cases hypbc with
              | inl hypbc =>
                -- Subcase 2.1: yb < ya ∧ yb < yc
                cases hypbc with
                | intro h'' hypbc =>
                  cases trichotomous (r := r) ya yc with
                  | inl h''' => -- yb < ya < yc
                    apply Or.inl
                    use h'''
                    exact (ihyp hyc).L_equiv_trans_lemma_center_lt_left_lt_right
                            ya h''' codea yb h'' codeb yc (Eq.refl yc) codec h' h'' h''' hypab hypbc
                  | inr h''' =>
                    apply Or.inr
                    cases h''' with
                    | inl h''' => -- yb < ya = yc
                      subst h'''
                      apply Or.inr
                      use (Eq.refl ya)
                      exact L_equiv_trans_lemma_outers_equal_gt_inner
                              ya hya codea yb hyb codeb ya hyc codec h' h'' (Eq.refl ya) hypab hypbc
                    | inr h''' => -- yb < yc < ya
                      apply Or.inl
                      use h'''
                      exact
                        (code_equiv_is_Equivalence ya (L (h := h) ya)).symm
                          ((ihyp hya).L_equiv_trans_lemma_center_lt_left_lt_right
                            yc h''' codec yb h' codeb ya (Eq.refl ya) codea h'' h' h'''
                              ((code_equiv_is_Equivalence yc (L (h := h) yc)).symm hypbc)
                              ((code_equiv_is_Equivalence ya (L (h := h) ya)).symm hypab))
              | inr hypbc =>
                cases hypbc with
                | inl hypbc =>
                  -- Subcase 2.2: yc < yb < ya
                  cases hypbc with
                  | intro h'' hypbc =>
                    apply Or.inr
                    apply Or.inl
                    let h''' := IsStrictOrder.toIsTrans.trans yc yb ya h'' h'
                    use h'''
                    exact
                      (code_equiv_is_Equivalence ya (L (h := h) ya)).symm
                        ((ihyp hya).L_equiv_trans_lemma_left_lt_center_lt_right
                          yc h''' codec yb h' codeb ya (Eq.refl ya) codea h'' h' h'''
                          ((code_equiv_is_Equivalence yb (L (h := h) yb)).symm hypbc)
                          ((code_equiv_is_Equivalence ya (L (h := h) ya)).symm hypab))
                | inr hypbc =>
                  -- Subcase 2.3: ya > yb = yc
                  cases hypbc with
                  | intro h'' hypbc =>
                    subst h''
                    dsimp at hypbc
                    apply Or.inr
                    apply Or.inl
                    use h'
                    exact (ihyp hya).L_equiv_trans_lemma_center_right_equal_lt_left
                      ya (Eq.refl ya) codea yb h' codeb yb h' codec h' (Eq.refl yb) h' hypab hypbc
          | inr hypab =>
            --Case 3: ya = yb
            cases hypab with
            | intro h' hypab =>
              subst h'
              dsimp at hypab
              cases hypbc with
              | inl hypbc =>
                -- Subcase 3.1: ya = yb < yc
                cases hypbc with
                | intro h'' hypbc =>
                  apply Or.inl
                  use h''
                  exact
                    (code_equiv_is_Equivalence yc (L (h := h) yc)).symm
                      ((ihyp hyc).L_equiv_trans_lemma_center_right_equal_lt_left
                        yc (Eq.refl yc) codec ya h'' codeb ya h'' codea h'' (Eq.refl ya) h''
                        ((code_equiv_is_Equivalence yc (L (h := h) yc)).symm hypbc)
                        ((code_equiv_is_Equivalence ya (L (h := h) ya)).symm hypab))
              | inr hypbc =>
                cases hypbc with
                | inl hypbc =>
                  -- Subcase 3.2: yc < yb = ya
                  cases hypbc with
                  | intro h' hypbc =>
                    apply Or.inr
                    apply Or.inl
                    use h'
                    exact
                      (code_equiv_is_Equivalence ya (L (h := h) ya)).symm
                        (L_equiv_trans_lemma_center_right_equal_gt_left
                         yc hyc codec ya hyb codeb ya hya codea h' (Eq.refl ya) h'
                          ((code_equiv_is_Equivalence ya (L (h := h) ya)).symm hypbc)
                          ((code_equiv_is_Equivalence ya (L (h := h) ya)).symm hypab))
                | inr hypbc =>
                  -- Subcase 3.3: ya = yb = yc
                  cases hypbc with
                  | intro h' hypbc =>
                    subst h'
                    dsimp at hypbc
                    apply Or.inr
                    apply Or.inr
                    use (Eq.refl ya)
                    dsimp
                    exact L_equiv_trans_lemma_all_equal
                            ya hya codea ya hyb codeb ya hyc codec
                            (Eq.refl ya) (Eq.refl ya) (Eq.refl ya) hypab hypbc
}

/-- This theorem shows that the membership relation for `L y3` respects the equality relation for
`L y3`. Thus, we are given elements `c ≈ c'` and `d ≈ d'` of `L y3`, with `c ∈ d`, and must show
`c' ∈ d'`. The 4 elements are codes of ranks `yc < y3`, `yc' < y3`, `yd < y3`, and `yd' < y3`
respectively. We lift this codes to codes of a common rank `z < y3` and use the theorem
`code_mem_respects_code_equiv` to do the main work. The precise details of the proof depend on 4
things: whether `yc < z` or `yc = z`, whether `yc' < z` or `yc' < yz`, etc. There are 16 possible
combinations of these possibilities, so there are 16 cases in the proof. The proof in each case
has a similar form: first we make substitutions of those variables of `yc`, `yc'`, `yd` and `yd'`
which equal `z` (replacing them with `z`), and then execute 5 `have` statements, which are each
done using macros defined earlier. Those are as follows: `step1...` converts the assumption `hcd`
into a membership statement at level `z`, the first `step2...` converts the equivalence between
`c`, `c'` at rank max(yc, yc') to one at z, the second `step2...` does likewise for `d`, `d'`,
`step4...` applies `code_mem_respects_code_equiv` at rank `z` to the foregoing things, and then
`step5...` converts the result of that to the desired fact about `L y3`. I did try to make the proof
uniform in cases, but had trouble in connection with type errors coming from the variables `yc` etc
collapsing to `z`. -/
theorem ind_L_seg_mem_respects_equiv
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_seg_mem_respects_equiv (y3 := y3) (h := h)
:=
    by
    unfold L_seg_mem_respects_equiv
    intro c c' d d' hcc' hdd' hcd
    match c, c', d, d' with
    | L_code_below.boundcode yc yc_LT codec,
      L_code_below.boundcode yc' yc'_LT codec',
      L_code_below.boundcode yd yd_LT coded,
      L_code_below.boundcode yd' yd'_LT coded' =>
    rcases upper_bound_of_4 (r:=r) (h := h) yc_LT yc'_LT yd_LT yd'_LT with ⟨z, jz, jc, jc', jd, jd'⟩
    cases jc with
    | inl jc =>
      cases jc' with
      | inl jc' =>
        cases jd with
        | inl jd =>
          cases jd' with
          | inl jd' =>
            --all < z (actually this case could have been eliminated by showing that we could
            --take z to be the max of c, c', d, d', but it's not difficult to handle it directly)
            let func := (ind_lift_codes_with_mem ihyp (h := h))
            step1_lt_lt hcd_z h yc yd z yc_LT yd_LT jz jc jd codec coded hcd func
            let func := (ind_lift_codes_with_equiv ihyp (h := h))
            step2_lt_lt hcc'_z h yc yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc' func
            step2_lt_lt hdd'_z h yd yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd' func
            step4_lt_lt hc'd'_z h yc' yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            let func := (ind_lift_codes_mem_iff ihyp (h := h))
            step5_lt_lt hc'd'_y3 h y3 yc' yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z func
            exact hc'd'_y3
          | inr jd' =>
            --yc, yc', yd < yd' = z
            have jd'_symm : z = yd' := jd'.symm
            subst jd'_symm
            let func := (ind_lift_codes_with_mem ihyp (h := h))
            step1_lt_lt hcd_z h yc yd z yc_LT yd_LT jz jc jd codec coded hcd func
            let func := (ind_lift_codes_with_equiv ihyp (h := h))
            step2_lt_lt hcc'_z h yc yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc' func
            step2_lt_eq hdd'_z h yd z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_first_code_equiv_iff
            step4_lt_eq hc'd'_z h yc' yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_lt_eq hc'd'_y3 h y3 yc' z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_first_code_mem_iff
            exact hc'd'_y3
        | inr jd =>
          cases jd' with
          | inl jd' =>
            --yc, yc', yd' < yd = z
            have jd_symm : z = yd := jd.symm
            subst jd_symm
            step1_lt_eq hcd_z h yc z z yc_LT yd_LT jz jc jd codec coded hcd lift_first_code_mem_iff
            let func := (ind_lift_codes_with_equiv ihyp (h := h))
            step2_lt_lt hcc'_z h yc yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc' func
            step2_eq_lt hdd'_z h z yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_second_code_equiv_iff
            step4_lt_lt hc'd'_z h yc' yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            let func := (ind_lift_codes_mem_iff ihyp (h := h))
            step5_lt_lt hc'd'_y3 h y3 yc' yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z func
            exact hc'd'_y3
          | inr jd' =>
            --yc, yc' < yd = yd' = z
            have jd_symm : z = yd := jd.symm
            have jd'_symm : z = yd' := jd'.symm
            subst jd_symm jd'_symm
            step1_lt_eq hcd_z h yc z z yc_LT yd_LT jz jc jd codec coded hcd lift_first_code_mem_iff
            let func := (ind_lift_codes_with_equiv ihyp (h := h))
            step2_lt_lt hcc'_z h yc yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc' func
            step2_eq_eq hdd'_z h z z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
            step4_lt_eq hc'd'_z h yc' z z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_lt_eq hc'd'_y3 h y3 yc' z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_first_code_mem_iff
            exact hc'd'_y3
      | inr jc' =>
        cases jd with
        | inl jd =>
          cases jd' with
          | inl jd' =>
            --yc, yd, yd' < yc' = z
            have jc'_symm : z = yc' := jc'.symm
            subst jc'_symm
            let func := (ind_lift_codes_with_mem ihyp (h := h))
            step1_lt_lt hcd_z h yc yd z yc_LT yd_LT jz jc jd codec coded hcd func
            step2_lt_eq hcc'_z h yc z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_first_code_equiv_iff
            let func := (ind_lift_codes_with_equiv ihyp (h := h))
            step2_lt_lt hdd'_z h yd yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd' func
            step4_eq_lt hc'd'_z h z yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_lt  hc'd'_y3 h y3 z yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_second_code_mem_iff
            exact hc'd'_y3
          | inr jd' =>
            --yc, yd < yc' = yd' = z
            have jc'_symm : z = yc' := jc'.symm
            have jd'_symm : z = yd' := jd'.symm
            subst jc'_symm jd'_symm
            let func := (ind_lift_codes_with_mem ihyp (h := h))
            step1_lt_lt hcd_z h yc yd z yc_LT yd_LT jz jc jd codec coded hcd func
            step2_lt_eq hcc'_z h yc z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_first_code_equiv_iff
            step2_lt_eq hdd'_z h yd z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_first_code_equiv_iff
            step4_eq_eq hc'd'_z h z z z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_eq hc'd'_y3 h y3 z z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
            exact hc'd'_y3
        | inr jd =>
          cases jd' with
          | inl jd' =>
            --yc, yd' < yd = yc' = z
            have jc'_symm : z = yc' := jc'.symm
            have jd_symm : z = yd := jd.symm
            subst jc'_symm jd_symm
            step1_lt_eq hcd_z h yc z z yc_LT yd_LT jz jc jd codec coded hcd
              lift_first_code_mem_iff
            step2_lt_eq hcc'_z h yc z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_first_code_equiv_iff
            step2_eq_lt hdd'_z h z yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_second_code_equiv_iff
            step4_eq_lt hc'd'_z h z yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_lt  hc'd'_y3 h y3 z yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_second_code_mem_iff
            exact hc'd'_y3
          | inr jd' =>
            --yc < yd = yc' = yd' = z
            have jc'_symm : z = yc' := jc'.symm
            have jd_symm : z = yd := jd.symm
            have jd'_symm : z = yd' := jd'.symm
            subst jc'_symm jd_symm jd'_symm
            step1_lt_eq hcd_z h yc z z yc_LT yd_LT jz jc jd codec coded hcd
              lift_first_code_mem_iff
            step2_lt_eq hcc'_z h yc z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_first_code_equiv_iff
            step2_eq_eq hdd'_z h z z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
            step4_eq_eq hc'd'_z h z z z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_eq hc'd'_y3 h y3 z z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
            exact hc'd'_y3
    | inr jc =>
      cases jc' with
      | inl jc' =>
        cases jd with
        | inl jd =>
          cases jd' with
          | inl jd' =>
            --yc', yd, yd' < yc = z
            have jc_symm : z = yc := jc.symm
            subst jc_symm
            step1_eq_lt hcd_z h z yd z yc_LT yd_LT jz jc jd codec coded hcd lift_second_code_mem_iff
            step2_eq_lt hcc'_z h z yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_second_code_equiv_iff
            let func := (ind_lift_codes_with_equiv ihyp (h := h))
            step2_lt_lt hdd'_z h yd yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd' func
            step4_lt_lt hc'd'_z h yc' yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            let func := (ind_lift_codes_mem_iff ihyp (h := h))
            step5_lt_lt hc'd'_y3 h y3 yc' yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z func
            exact hc'd'_y3
          | inr jd' =>
            --yc', yd < yc = yd' = z
            have jc_symm : z = yc := jc.symm
            have jd'_symm : z = yd' := jd'.symm
            subst jc_symm jd'_symm
            step1_eq_lt hcd_z h z yd z yc_LT yd_LT jz jc jd codec coded hcd lift_second_code_mem_iff
            step2_eq_lt hcc'_z h z yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_second_code_equiv_iff
            step2_lt_eq hdd'_z h yd z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_first_code_equiv_iff
            step4_lt_eq hc'd'_z h yc' yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_lt_eq hc'd'_y3 h y3 yc' z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_first_code_mem_iff
            exact hc'd'_y3
        | inr jd =>
          cases jd' with
          | inl jd' =>
            --yc', yd' < yc = yd = z
            have jc_symm : z = yc := jc.symm
            have jd_symm : z = yd := jd.symm
            subst jc_symm jd_symm
            step1_eq_eq hcd_z h z z z yc_LT yd_LT jz jc jd codec coded hcd
            step2_eq_lt hcc'_z h z yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_second_code_equiv_iff
            step2_eq_lt hdd'_z h z yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_second_code_equiv_iff
            step4_lt_lt hc'd'_z h yc' yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            let func := (ind_lift_codes_mem_iff ihyp (h := h))
            step5_lt_lt hc'd'_y3 h y3 yc' yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z func
            exact hc'd'_y3
          | inr jd' =>
            --yc' < yc = yd = yd' = z
            have jc_symm : z = yc := jc.symm
            have jd_symm : z = yd := jd.symm
            have jd'_symm : z = yd' := jd'.symm
            subst jc_symm jd_symm jd'_symm
            step1_eq_eq hcd_z h z z z yc_LT yd_LT jz jc jd codec coded hcd
            step2_eq_lt hcc'_z h z yc' z yc_LT yc'_LT jz jc jc' codec codec' hcc'
              lift_second_code_equiv_iff
            step2_eq_eq hdd'_z h z z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
            step4_lt_eq hc'd'_z h yc' z z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_lt_eq hc'd'_y3 h y3 yc' z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_first_code_mem_iff
            exact hc'd'_y3
      | inr jc' =>
        cases jd with
        | inl jd =>
          cases jd' with
          | inl jd' =>
            --yd, yd' < yc = yc' = z
            have jc_symm : z = yc := jc.symm
            have jc'_symm : z = yc' := jc'.symm
            subst jc_symm jc'_symm
            step1_eq_lt hcd_z h z yd z yc_LT yd_LT jz jc jd codec coded hcd lift_second_code_mem_iff
            step2_eq_eq hcc'_z h z z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
            let func := (ind_lift_codes_with_equiv ihyp (h := h))
            step2_lt_lt hdd'_z h yd yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd' func
            step4_eq_lt hc'd'_z h z yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_lt  hc'd'_y3 h y3 z yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_second_code_mem_iff
            exact hc'd'_y3
          | inr jd' =>
            --yd < yc = yc' = yd' = z
            have jc_symm : z = yc := jc.symm
            have jc'_symm : z = yc' := jc'.symm
            have jd'_symm : z = yd' := jd'.symm
            subst jc_symm jc'_symm jd'_symm
            step1_eq_lt hcd_z h z yd z yc_LT yd_LT jz jc jd codec coded hcd lift_second_code_mem_iff
            step2_eq_eq hcc'_z h z z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
            step2_lt_eq hdd'_z h yd z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_first_code_equiv_iff
            step4_eq_eq hc'd'_z h z z z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_eq hc'd'_y3 h y3 z z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
            exact hc'd'_y3
        | inr jd =>
          cases jd' with
          | inl jd' =>
            --yd' < yc = yd = yc' = z
            have jc_symm : z = yc := jc.symm
            have jc'_symm : z = yc' := jc'.symm
            have jd_symm : z = yd := jd.symm
            subst jc_symm jc'_symm jd_symm
            step1_eq_eq hcd_z h z z z yc_LT yd_LT jz jc jd codec coded hcd
            step2_eq_eq hcc'_z h z z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
            step2_eq_lt hdd'_z h z yd' z yd_LT yd'_LT jz jd jd' coded coded' hdd'
              lift_second_code_equiv_iff
            step4_eq_lt hc'd'_z h z yd' z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_lt  hc'd'_y3 h y3 z yd' z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
              lift_second_code_mem_iff
            exact hc'd'_y3
          | inr jd' =>
            --yc = yd = yc' = yd' = z
            have jc_symm : z = yc := jc.symm
            have jc'_symm : z = yc' := jc'.symm
            have jd_symm : z = yd := jd.symm
            have jd'_symm : z = yd' := jd'.symm
            subst jc_symm jc'_symm jd_symm jd'_symm
            step1_eq_eq hcd_z h z z z yc_LT yd_LT jz jc jd codec coded hcd
            step2_eq_eq hcc'_z h z z z yc_LT yc'_LT jz jc jc' codec codec' hcc'
            step2_eq_eq hdd'_z h z z z yd_LT yd'_LT jz jd jd' coded coded' hdd'
            step4_eq_eq hc'd'_z h z z z jc' jd' codec' coded' hcc'_z hdd'_z hcd_z
            step5_eq_eq hc'd'_y3 h y3 z z z yc'_LT yd'_LT jz jc' jd' codec' coded' hc'd'_z
            exact hc'd'_y3

/-- One quarter of extensionality. Note that it only does → in the implication between the
membership statements. -/
theorem ind_L_extensional_equiv_implies_mp
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_extensional_equiv_implies_mp (y3 := y3) (h := h)
:=
    by
    unfold L_extensional_equiv_implies_mp
    intro d d' hyp z hyp2
    exact (ind_L_seg_mem_respects_equiv ihyp) z z d d'
            ((ind_L_seg_equiv_is_Equivalence ihyp).refl z) hyp hyp2

/-- One half of extensionality. It has the ↔ between the membership statements. -/
theorem ind_L_extensional_equiv_implies
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_extensional_equiv_implies (y3 := y3) (h := h)
:=
    by
    unfold L_extensional_equiv_implies
    intro d d' hyp x
    apply Iff.intro
    · exact (ind_L_extensional_equiv_implies_mp ihyp) d d' hyp x
    · have hyp' : (L (h := h) y3).equiv d' d := (ind_L_seg_equiv_is_Equivalence ihyp).symm hyp
      exact (ind_L_extensional_equiv_implies_mp ihyp) d' d hyp' x

theorem ind_code_equiv_iff
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: code_equiv_iff (y3 := y3) (h := h)
:=
    by
    unfold code_equiv_iff
    intro y hy_LT c c'
    apply Iff.intro
    · intro hyp
      unfold code_equiv at hyp
      intro x jx codex
      let x' := L_code_below.boundcode x jx codex
      have hypx' : sats_L_code_param (L y) c x' ↔ sats_L_code_param (L y) c' x'
      := hyp x'
      unfold code_mem
      apply Iff.intro
      · intro hyp2
        cases hyp2 with
        | intro p hyp2' =>
          use p
          apply And.intro
          · intro x_1
            rw[sats_L_code_param_of_lift_code x  jx  codex x_1]
            have k : sats_L_code_param (L y) (lift_code x y jx codex) x_1 ↔ (L y).mem x_1 p
            := hyp2'.1 x_1
            rw[sats_L_code_param_of_lift_code x jx codex x_1] at k
            exact k
          · exact (hyp p).mp hyp2'.2
      · intro hyp2
        cases hyp2 with
        | intro p hyp2' =>
          use p
          apply And.intro
          · intro x_1
            rw[sats_L_code_param_of_lift_code x  jx  codex x_1]
            have k : sats_L_code_param (L y) (lift_code x y jx codex) x_1 ↔ (L y).mem x_1 p
            := hyp2'.1 x_1
            rw[sats_L_code_param_of_lift_code x jx codex x_1] at k
            exact k
          · exact (hyp p).mpr hyp2'.2
    · intro hyp
      unfold code_equiv
      intro x
      cases x with
      | boundcode yx jx codex =>
        have j :     code_mem (L y) (lift_code yx y jx codex) c
                  ↔  code_mem (L y) (lift_code yx y jx codex) c'
        := hyp yx jx codex
        unfold code_mem at j
        apply Iff.intro
        · intro hyp2
          have i : ∃ p, (∀ (x_1 : L_univ y),
                          ((sats_L_code_param (L y) (lift_code yx y jx codex) x_1)
                          ↔ ((L (h := h) y).mem x_1 p))) ∧ (sats_L_code_param (L y) c p)
          := ⟨(L_code_below.boundcode yx jx codex),
              ⟨fun x_1 => (sats_L_code_param_of_lift_code yx jx codex x_1),hyp2⟩⟩
          have i' : ∃ p,  (∀ (x_1 : L_univ y),
                              ((sats_L_code_param (L y) (lift_code yx y jx codex) x_1)
                              ↔ ((L (h := h) y).mem x_1 p))) ∧ (sats_L_code_param (L y) c' p)
          := j.mp i
          cases i' with
          | intro p i'' =>
            have j' : ∀ (x_1 : L_univ y),
                        ((L (h := h) y).mem x_1 (L_code_below.boundcode yx jx codex)
                        ↔ ((L (h := h) y).mem x_1 p))
            :=
              by
              intro x_1
              have i''1x_1 : (sats_L_code_param (L y) (lift_code yx y jx codex) x_1)
                             ↔ ((L y).mem x_1 p)
              := i''.1 x_1
              rw [sats_L_code_param_of_lift_code yx jx codex x_1] at i''1x_1
              exact i''1x_1
            have k : sats_L_code_param (L y) c' p
            := i''.2
            have l : (L (h := h) y).equiv p (L_code_below.boundcode yx jx codex)
            :=  ((ihyp hy_LT).L_extensional p (L_code_below.boundcode yx jx codex)).mpr
                  (fun x => (j' x).symm)
            exact (ihyp hy_LT).sats_L_code_param_respects_equiv_param c' l k
        · intro hyp2
          have i : ∃ p, (∀ (x_1 : L_univ y),
                          ((sats_L_code_param (L y) (lift_code yx y jx codex) x_1)
                          ↔ ((L (h := h) y).mem x_1 p))) ∧ (sats_L_code_param (L y) c' p)
          := ⟨(L_code_below.boundcode yx jx codex),
              ⟨fun x_1 => (sats_L_code_param_of_lift_code yx jx codex x_1),hyp2⟩⟩
          have i' : ∃ p, (∀ (x_1 : L_univ y),
                            ((sats_L_code_param (L y) (lift_code yx y jx codex) x_1)
                            ↔ ((L (h := h) y).mem x_1 p))) ∧ (sats_L_code_param (L y) c p)
          := j.mpr i
          cases i' with
          | intro p i'' =>
            have j' : ∀ (x_1 : L_univ y),
                        ((L (h := h) y).mem x_1 (L_code_below.boundcode yx jx codex)
                        ↔ ((L (h := h) y).mem x_1 p))
            :=
              by
              intro x_1
              have i''1x_1 :  (sats_L_code_param (L y) (lift_code yx y jx codex) x_1)
                              ↔ ((L y).mem x_1 p)
              := i''.1 x_1
              rw [sats_L_code_param_of_lift_code yx jx codex x_1] at i''1x_1
              exact i''1x_1
            have k : sats_L_code_param (L y) c p
            := i''.2
            have l : (L (h := h) y).equiv p (L_code_below.boundcode yx jx codex)
            :=  ((ihyp hy_LT).L_extensional p (L_code_below.boundcode yx jx codex)).mpr
                  (fun x => (j' x).symm)
            exact (ihyp hy_LT).sats_L_code_param_respects_equiv_param c l k

theorem ind_L_extensional_mem_implies
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_extensional_mem_implies (y3 := y3) (h := h)
:=
    by
    unfold L_extensional_mem_implies
    intro d d' hyp
    match d, d' with
    | L_code_below.boundcode yd yd_LT coded,
      L_code_below.boundcode yd' yd'_LT coded' =>
    rw [L_seg_equiv]
    dsimp
    unfold L_recursion_trichotomy_equiv
    cases h.toTrichotomous.rel_or_eq_or_rel_swap  (a:=yd) (b:=yd') with
    | inl jdd' => --Case yd < yd'
      apply Or.inl
      use jdd'
      rw [(ind_code_equiv_iff ihyp) yd' yd'_LT]
      intro x jx codex
      have hypc
      :   (L y3).mem (L_code_below.boundcode
                        x (IsStrictOrder.toIsTrans.trans x yd' y3 jx yd'_LT) codex)
                     (L_code_below.boundcode yd yd_LT coded)
        ↔ (L y3).mem (L_code_below.boundcode
                        x (IsStrictOrder.toIsTrans.trans x yd' y3 jx yd'_LT) codex)
                     (L_code_below.boundcode yd' yd'_LT coded')
      := hyp (L_code_below.boundcode x (IsStrictOrder.toIsTrans.trans x yd' y3 jx yd'_LT) codex)
      rw [L_seg_mem_of_constructed_boundcodes_first_below_second x yd'
            (IsStrictOrder.toIsTrans.trans x yd' y3 jx yd'_LT) yd'_LT jx codex coded']
        at hypc
      rw [(ind_lift_codes_mem_iff ihyp) x yd yd' yd'_LT
            (IsStrictOrder.toIsTrans.trans x yd' y3 jx yd'_LT) yd_LT jx jdd' codex coded]
        at hypc
      exact hypc
    | inr jdd' =>
    cases jdd' with
    | inl jdd' => --Case yd = yd'
      subst jdd'
      dsimp
      apply Or.inr
      apply Or.inr
      use (Eq.refl yd)
      rw [(ind_code_equiv_iff ihyp) yd yd_LT]
      intro x jx codex
      have hypc
      :   (L y3).mem  (L_code_below.boundcode
                        x (IsStrictOrder.toIsTrans.trans x yd y3 jx yd'_LT) codex)
                      (L_code_below.boundcode yd yd_LT coded)
        ↔ (L y3).mem  (L_code_below.boundcode
                        x (IsStrictOrder.toIsTrans.trans x yd y3 jx yd'_LT) codex)
                      (L_code_below.boundcode yd yd'_LT coded')
      := hyp (L_code_below.boundcode x (IsStrictOrder.toIsTrans.trans x yd y3 jx yd'_LT) codex)
      rw [L_seg_mem_of_constructed_boundcodes_first_below_second
            x yd (IsStrictOrder.toIsTrans.trans x yd y3 jx yd'_LT) yd'_LT jx codex coded'] at hypc
      rw [L_seg_mem_of_constructed_boundcodes_first_below_second
            x yd (IsStrictOrder.toIsTrans.trans x yd y3 jx yd_LT) yd_LT jx codex coded] at hypc
      exact hypc
    | inr jdd' => --Case yd' < yd
      apply Or.inr
      apply Or.inl
      use jdd'
      rw [(ind_code_equiv_iff ihyp) yd yd_LT]
      intro x jx codex
      have hypc
      :   (L y3).mem  (L_code_below.boundcode
                        x (IsStrictOrder.toIsTrans.trans x yd y3 jx yd_LT) codex)
                      (L_code_below.boundcode yd yd_LT coded)
        ↔ (L y3).mem  (L_code_below.boundcode
                        x (IsStrictOrder.toIsTrans.trans x yd y3 jx yd_LT) codex)
                      (L_code_below.boundcode yd' yd'_LT coded')
      := hyp (L_code_below.boundcode
                x (IsStrictOrder.toIsTrans.trans x yd y3 jx yd_LT) codex)
      rw [L_seg_mem_of_constructed_boundcodes_first_below_second
            x yd (IsStrictOrder.toIsTrans.trans x yd y3 jx yd_LT) yd_LT jx codex coded] at hypc
      rw [(ind_lift_codes_mem_iff ihyp) x yd' yd yd_LT
          (IsStrictOrder.toIsTrans.trans x yd y3 jx yd_LT) yd'_LT jx jdd' codex coded']
        at hypc
      exact hypc

theorem ind_L_extensional
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_extensional (y3 := y3) (h := h)
:=
    by
    unfold L_extensional
    intro d d'
    apply Iff.intro
    · exact (ind_L_extensional_equiv_implies ihyp) d d'
    · exact (ind_L_extensional_mem_implies ihyp) d d'

theorem ind_lift_code_equiv_emb
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: lift_code_equiv_emb (y3 := y3) (h := h)
:=
    by
    unfold lift_code_equiv_emb
    intro y1 h13 code1 code2
    let boundcode1 := L_code_below.boundcode y1 h13 code1
    let boundcode2 := L_code_below.boundcode y1 h13 code2
    have i : (L (h := h) y3).equiv boundcode1 boundcode2 ↔ code_equiv (L (h := h) y1) code1 code2
    := L_seg_equiv_of_constructed_boundcodes_same_level y1 h13 code1 code2
    apply Iff.intro
    · intro hyp
      unfold code_equiv
      intro x
      rw [sats_L_code_param_of_lift_code]
      rw [sats_L_code_param_of_lift_code]
      have j : (L y3).mem x boundcode1 ↔ (L y3).mem x boundcode2
      := ((ind_L_extensional ihyp) boundcode1 boundcode2).mp (i.mpr hyp) x
      exact j
    · intro hyp
      unfold code_equiv at hyp
      have j : (L (h := h) y3).equiv boundcode1 boundcode2
      :=
        by
        apply ((ind_L_extensional ihyp) boundcode1 boundcode2).mpr
        intro x
        have hypx : sats_L_code_param (L y3) (lift_code y1 y3 h13 code1) x
        ↔ sats_L_code_param (L y3) (lift_code y1 y3 h13 code2) x
        := hyp x
        rw [sats_L_code_param_of_lift_code] at hypx
        rw [sats_L_code_param_of_lift_code] at hypx
        exact hypx
      exact i.mp j

theorem ind_L_equiv_trans_lemma_outers_equal_lt_inner
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_equiv_trans_lemma_outers_equal_lt_inner (y3 := y3) (h := h)
:=
  by
  unfold L_equiv_trans_lemma_outers_equal_lt_inner
  intro ya hya codea yb hyb codeb yc hyc codec hyab hybc hyac equiv_ab equiv_bc
  subst hyac hyb
  dsimp
  have i
  : code_equiv (L (h := h) yb) (lift_code ya yb hyab codea) (lift_code ya yb hyab codec)
  := (code_equiv_is_Equivalence yb (L (h := h) yb)).trans equiv_ab equiv_bc
  exact ((ind_lift_code_equiv_emb ihyp) hyab codea codec).mpr i

theorem ind_L_equiv_trans_lemma_center_right_equal_lt_left
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_equiv_trans_lemma_center_right_equal_lt_left (y3 := y3) (h := h)
:=
  by
  unfold L_equiv_trans_lemma_center_right_equal_lt_left
  intro ya hya codea yb hyb codeb yc hyc codec hyab hybc hyac equiv_ab equiv_bc
  subst hybc hya
  dsimp at equiv_bc
  have equiv_bc_at_ya
  : code_equiv (L (h := h) ya) (lift_code yb ya hyab codeb) (lift_code yb ya hyac codec)
  := ((ind_lift_code_equiv_emb ihyp) hyab codeb codec).mp (equiv_bc)
  exact (code_equiv_is_Equivalence ya (L (h := h) ya)).trans equiv_ab equiv_bc_at_ya

theorem ind_L_equiv_trans_lemma_center_lt_left_lt_right
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_equiv_trans_lemma_center_lt_left_lt_right (y3 := y3) (h := h)
:=
    by
    unfold L_equiv_trans_lemma_center_lt_left_lt_right
    intro ya hya codea yb hyb codeb yc hyc codec hyab hybc hyac equiv_ab equiv_bc
    subst hyc
    have equiv_ab_lifted
    : code_equiv (L (h := h) yc) (lift_code ya yc hyac codea)
        (lift_code ya yc hyac (lift_code yb ya hyab codeb))
    := ((ind_lift_code_equiv_emb ihyp) hyac codea (lift_code yb ya hyab codeb)).mp equiv_ab
    have commuting_lift_codes
    : code_equiv (L (h := h) yc) (lift_code ya yc hyac (lift_code yb ya hyab codeb))
        (lift_code yb yc hybc codeb)
    :=  (code_equiv_is_Equivalence yc (L (h := h) yc)).symm
          ((ind_lift_code_commutes ihyp) ya yb hyac hyab hybc codeb)
    exact (code_equiv_is_Equivalence yc (L (h := h) yc)).trans equiv_ab_lifted
      ((code_equiv_is_Equivalence yc (L (h := h) yc)).trans commuting_lift_codes equiv_bc)

theorem ind_L_equiv_trans_lemma_left_lt_center_lt_right
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
  : L_equiv_trans_lemma_left_lt_center_lt_right (y3 := y3) (h := h)
  :=
    by
    unfold L_equiv_trans_lemma_left_lt_center_lt_right
    intro ya hya codea yb hyb codeb yc hyc codec hyab hybc hyac equiv_ab equiv_bc
    subst hyc
    have equiv_ab_lifted
    : code_equiv (L (h := h) yc) (lift_code yb yc hybc (lift_code ya yb hyab codea))
        (lift_code yb yc hybc codeb)
    := ((ind_lift_code_equiv_emb ihyp) hybc (lift_code ya yb hyab codea) codeb).mp equiv_ab
    have commuting_lift_codes
    : code_equiv (L (h := h) yc) (lift_code yb yc hybc (lift_code ya yb hyab codea))
        (lift_code ya yc hyac codea)
    :=  (code_equiv_is_Equivalence yc (L (h := h) yc)).symm
          ((ind_lift_code_commutes ihyp) yb ya hybc hyab hyac codea)
    exact (code_equiv_is_Equivalence yc (L (h := h) yc)).trans
            ((code_equiv_is_Equivalence yc (L (h := h) yc)).symm commuting_lift_codes)
            ((code_equiv_is_Equivalence yc (L (h := h) yc)).trans equiv_ab_lifted equiv_bc)

theorem ind_L_equiv_trans_lemma_left_lt_right_lt_center
    {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: L_equiv_trans_lemma_left_lt_right_lt_center (y3 := y3) (h := h)
:=
    by
    unfold L_equiv_trans_lemma_left_lt_right_lt_center
    intro ya hya codea yb hyb codeb yc hyc codec hyab hybc hyac equiv_ab equiv_bc
    subst hyb
    have equiv_ac_at_yb
    : code_equiv (L (h := h) yb) (lift_code ya yb hyab codea) (lift_code yc yb hybc codec)
    := (code_equiv_is_Equivalence yb (L (h := h) yb)).trans equiv_ab equiv_bc
    have commuting_lift_codes
    : code_equiv (L (h := h) yb) (lift_code yc yb hybc (lift_code ya yc hyac codea))
        (lift_code ya yb hyab codea)
    :=  (code_equiv_is_Equivalence yb (L (h := h) yb)).symm
          ((ind_lift_code_commutes ihyp) yc ya hybc hyac hyab codea)
    have equiv_ac_factored
    : code_equiv (L (h := h) yb) (lift_code yc yb hybc (lift_code ya yc hyac codea))
        (lift_code yc yb hybc codec)
    := (code_equiv_is_Equivalence yb (L (h := h) yb)).trans commuting_lift_codes equiv_ac_at_yb
    exact ((ind_lift_code_equiv_emb ihyp) hybc
            (lift_code ya yc hyac codea) codec).mpr equiv_ac_factored

theorem ind_sats_L_code_param_respects_equiv_param
  {y3 : α}
  (ihyp : ext_IH y3 (h := h))
: sats_L_code_param_respects_equiv_param (y3 := y3) (h := h)
:=
  by
  unfold sats_L_code_param_respects_equiv_param
  intro c p q hpq hsats
  unfold sats_L_code_param at hsats
  unfold sats_L_code_param
  set M := LSTModel.mk (L_univ  y3) (L (h:=h) y3).equiv (L (h:=h) y3).mem
  have M_eq_Equiv
  : Equivalence M.eq
  := ind_L_seg_equiv_is_Equivalence ihyp
  have M_mem_respects
  : respects M.eq M.mem
  := ind_L_seg_mem_respects_equiv ihyp
  set StandardM := StandardLSTModel.mk M M_eq_Equiv M_mem_respects
  dsimp
  cases c with
  | code φ v σ hσ τ =>
    dsimp only
    dsimp at hsats
    have hτ : σ.length = (to_List τ).length :=  (L_ListToListLength τ).symm
    set p_ass := build_ass M φ v σ hσ (to_List τ) hτ p
    set q_ass := build_ass M φ v σ hσ (to_List τ) hτ q
    have p_q_ass_equiv
    : equiv_ass (StandardLSTModel.mk M (heq:=M_eq_Equiv) (hmem:=M_mem_respects)) φ p_ass q_ass
    :=by
      unfold equiv_ass
      intro w hw
      if hvw : v = w then
        --in this case one evaluates to p, one to q
        subst hvw
        have var_eval_p_ass_eq_p
        : var_eval p_ass v (p_ass.hfree_var.2 hw) = p
        := eval_build_ass_on_new_var (α:=α) M φ v σ hσ (to_List τ) hτ p hw
        have var_eval_q_ass_eq_q
        : var_eval q_ass v (q_ass.hfree_var.2 hw) = q
        := eval_build_ass_on_new_var (α:=α) M φ v σ hσ (to_List τ) hτ q hw
        exact var_eval_q_ass_eq_q ▸ var_eval_p_ass_eq_p.symm ▸ hpq
      else
        --in this case they eval to the same object
        have w_in_σ : w ∈ σ
        := List_mem_respects_ext_equiv_mp var (free_var_excluding φ v) σ hσ.2.symm w
          (variable_in_free_var_neq_excluded_is_in_free_var_excluding φ v w hvw hw)
        have var_eval_p_ass_eq_var_eval_q_ass
        : var_eval p_ass w (p_ass.hfree_var.2 hw) = var_eval q_ass w (q_ass.hfree_var.2 hw)
        :=(eval_build_ass_on_old_var (α:=α) M φ v w σ hσ (to_List τ) hτ p w_in_σ).trans
            (eval_build_ass_on_old_var M φ v w σ hσ (α:=α) (to_List τ) hτ q w_in_σ).symm
        rw[var_eval_p_ass_eq_var_eval_q_ass]
        exact M_eq_Equiv.refl (var_eval q_ass w (q_ass.hfree_var.2 hw))
    exact sats_respects_equiv StandardM φ p_ass q_ass p_q_ass_equiv hsats

theorem ind_lift_code_mem_emb {y3 : α}
    (ihyp : ext_IH y3 (h := h))
: lift_code_mem_emb (y3 := y3) (h := h)
:=
    by
    unfold lift_code_mem_emb
    intro y1 h13 code1 code2
    let boundcode1 := L_code_below.boundcode y1 h13 code1
    let boundcode2 := L_code_below.boundcode y1 h13 code2
    apply Iff.intro
    · intro hyp
      unfold code_mem
      use boundcode1
      apply And.intro
      · intro x
        rw [sats_L_code_param_of_lift_code]
      · rw [sats_L_code_param_of_lift_code]
        exact (L_seg_mem_of_constructed_boundcodes_same_level y1 h13 code1 code2).mpr hyp
    · intro hyp
      unfold code_mem at hyp
      cases hyp with
      | intro p hyp' =>
        have i : (L (h := h) y3).equiv p boundcode1
        :=
          by
          apply ((ind_L_extensional ihyp) p boundcode1).mpr
          intro x
          let hyp'1x := hyp'.1 x
          rw [sats_L_code_param_of_lift_code] at hyp'1x
          exact Iff.symm hyp'1x
        let hyp'2 := hyp'.2
        rw [sats_L_code_param_of_lift_code] at hyp'2
        have hyp'2boundcode : (L y3).mem boundcode1 boundcode2
        :=  (ind_L_seg_mem_respects_equiv ihyp) p boundcode1 boundcode2 boundcode2 i
              ((ind_L_seg_equiv_is_Equivalence ihyp).refl boundcode2) hyp'2
        exact (L_seg_mem_of_constructed_boundcodes_same_level y1 h13 code1 code2).mp hyp'2boundcode

theorem L_ext_inductive_step (y : α) (ihyp : ext_IH y (h := h))
: L_ext_inductive_properties y (h := h)
:= {L_equiv_trans_lemma_outers_equal_lt_inner :=
      ind_L_equiv_trans_lemma_outers_equal_lt_inner (y3 := y) (h := h) ihyp
    L_equiv_trans_lemma_center_right_equal_lt_left :=
      ind_L_equiv_trans_lemma_center_right_equal_lt_left (y3 := y) (h := h) ihyp
    L_equiv_trans_lemma_center_lt_left_lt_right :=
      ind_L_equiv_trans_lemma_center_lt_left_lt_right (y3 := y) (h := h) ihyp
    L_equiv_trans_lemma_left_lt_center_lt_right :=
      ind_L_equiv_trans_lemma_left_lt_center_lt_right (y3 := y) (h := h) ihyp
    L_equiv_trans_lemma_left_lt_right_lt_center :=
      ind_L_equiv_trans_lemma_left_lt_right_lt_center (y3 := y) (h := h) ihyp
    L_seg_equiv_is_Equivalence := ind_L_seg_equiv_is_Equivalence (y3 := y) (h := h) ihyp
    lift_codes_with_mem := ind_lift_codes_with_mem (y3 := y) (h := h) ihyp
    lift_codes_with_equiv := ind_lift_codes_with_equiv (y3 := y) (h := h) ihyp
    lift_codes_mem_iff := ind_lift_codes_mem_iff (y3 := y) (h := h) ihyp
    L_seg_mem_respects_equiv := ind_L_seg_mem_respects_equiv (y3 := y) (h := h) ihyp
    L_extensional_equiv_implies_mp := ind_L_extensional_equiv_implies_mp (y3 := y) (h := h) ihyp
    L_extensional_equiv_implies := ind_L_extensional_equiv_implies (y3 := y) (h := h) ihyp
    code_equiv_iff := ind_code_equiv_iff (y3 := y) (h := h) ihyp
    L_extensional_mem_implies := ind_L_extensional_mem_implies (y3 := y) (h := h) ihyp
    L_extensional := ind_L_extensional (y3 := y) (h := h) ihyp
    sats_L_code_param_respects_equiv_param :=
      ind_sats_L_code_param_respects_equiv_param (y3 := y) (h := h) ihyp
    lift_code_commutes := ind_lift_code_commutes (y3 := y) (h := h) ihyp
    lift_code_equiv_emb := ind_lift_code_equiv_emb (y3 := y) (h := h) ihyp
    lift_code_mem_emb := ind_lift_code_mem_emb (y3 := y) (h := h) ihyp}

theorem L_ext_properties (y : α) : L_ext_inductive_properties y (h:=h)
:= WellFounded.fix h.wf L_ext_inductive_step y

end LL
