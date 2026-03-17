/-
Copyright (c) 2026 Farmer Schlutzenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Farmer Schlutzenberg, https://sites.google.com/site/schlutzenberg
-/
import Mathlib.Order.RelClasses
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.setOption false

--set_option pp.coercions true

universe u u'

--Lists
/-Lists: In this section we develop some basic material on lists and the *extensional equivalence* relation.
We work with `List.cons` (note `(List.cons x s) = (x::s)`), `List.erase`, `List.insert`, `x ∈ s` and `s ⊆ t` (for lists `s`, `t`), `List.Nodup` ("no duplications" or "duplication-free").
Most things will be developed for the type `List α`, where `α` is a type satisfying `DecidableEq α`.-/
section Lists

--Some useful basic tools:
#check List.mem_insert_iff
#check List.mem_cons
#check List.mem_cons_self
#check List.mem_cons_of_mem
#check List.Nodup.erase
#check List.Nodup.cons
#check List.nodup_nil
#check List.not_mem_nil
#check List.length_cons
#check List.mem_erase_of_ne
#check List.erase_subset
#check List.cons_ne_nil
#check List.nodup_cons
#check List.length_erase_add_one
#check List.length
#check List.length_pos_of_mem
#check List.length_nil
#check Nat.lt_irrefl

variable (α:Type u) [DecidableEq α]

/--Definition: Two lists `s, t` (of type `List α`) are *extensionally equivalent* (`ext_equiv`) if each is a subset of the other: `s ⊆ t ∧ t ⊆ s`.-/
def ext_equiv (s t : List α) : Prop := s ⊆ t ∧ t ⊆ s

/--Theorem: `ext_equiv` is an equivalence relation (satisfies `Equivalence`).-/
theorem ext_equiv_is_Equivalence  : Equivalence (ext_equiv (α:=α)) where
  -- Must prove `∀ (s:List α) : ext_equiv s s`
  refl (s : List α) := ⟨List.Subset.refl s, List.Subset.refl s⟩
  -- Must prove `∀ s t, ext_equiv s t → ext_equiv t s`
  symm {s t : List α} (h : ext_equiv (α:=α) s t) := ⟨h.right,h.left⟩
  -- Must prove `∀ (r s t : List α), (ext_equiv r s) → (ext_equiv s t) → ext_equiv r t`.
  trans {r s t : List α} (hrs : ext_equiv (α:=α) r s) (hst : ext_equiv (α:=α) s t):=
    ⟨List.Subset.trans hrs.left hst.left,List.Subset.trans hst.right hrs.right⟩

/--Instance: `ext_equiv` yields a `Setoid` instance; we henceforth use `≈` for `ext_equiv`-/
instance (priority := 4294967295): Setoid  (List α) where
  r := ext_equiv α
  iseqv := ext_equiv_is_Equivalence α

/--Lemma: For lists `s`, `t`, if `x ∈ s ≈ t` then `x ∈ t`. (Lemma toward theorem `List_mem_respects_ext_equiv`)-/
theorem List_mem_respects_ext_equiv_mp
  (s t : List α)
  (h : s≈ t)
  (x:α)
  (i : x∈ s)
: x ∈ t
:= h.1 i

/--Theorem: List membership respects `≈`-/
theorem List_mem_respects_ext_equiv
  (s t : List α)
  (h : s≈ t)
  (x:α)
: x∈ s ↔ x∈ t
:=
  Iff.intro
    (fun (i:x∈ s) => List_mem_respects_ext_equiv_mp (α:=α) s t h x i)
    (fun (i:x∈ t) => List_mem_respects_ext_equiv_mp (α:=α) t s h.symm x i)

/--Theorem: List non-membership respects `≈`-/
theorem List_non_mem_respects_ext_equiv
  (s t : List α)
  (h : s≈ t)
  (x:α)
  (i : x∉ s)
: x∉ t
:= (List_mem_respects_ext_equiv (α:=α) s t h x).mpr.mt i

/--Theorem: Given lists `s`, `t`, if `s ⊆ t` then `(v::s) ⊆ (v::t)`.-/
theorem List_subset_implies_cons_subset
  {s t : List α}
  (v:α)
  (h : s ⊆ t)
: (v :: s) ⊆ (v :: t)
:=
  by
  intro x
  intro i
  rw [List.mem_cons] at i
  rw [List.mem_cons]
  cases i with
  | inl j => exact Or.inl j
  | inr j => exact Or.inr (h j)

/--Theorem: `List.cons` (with the same head added) respects `≈` -/
theorem List_cons_respects_ext_equiv
  {s t : List α}
  (v:α)
  (h : s ≈ t)
: (v :: s) ≈ (v :: t)
:= ⟨(List_subset_implies_cons_subset (α:=α) v h.1),
    (List_subset_implies_cons_subset (α:=α) v h.2)⟩

/--Theorem: If `s ≠ []` is then `¬ (s ≈ [])` (the empty list).-/
theorem List_nil_not_ext_equiv_non_nil
  {s : List α}
  (h : s ≠ ([]:List α))
: ¬(s ≈ ([]:List α))
:=
  match s with
  | List.nil => by contradiction
  | List.cons x s' => by
    have i : x ∉ [] := List.not_mem_nil
    have j : x ∈ (x::s') := List.mem_cons_self
    intro k
    have l : x ∈ [] := k.1 j
    contradiction

/--Theorem: If `v ∈ s` (list `s`) then erasing `v` followed by inserting `v` results in a list `≈ s`.-/
theorem List_insert_erase
  (s : List α)
  (v : α)
  (h : v ∈ s)
: List.insert v (s.erase v) ≈ s
:= by
  apply And.intro
  · intro x i
    rw[List.mem_insert_iff] at i
    apply Or.elim i
    · intro j
      rw [← j] at h
      exact h
    · intro j
      apply List.erase_subset (a:=v) (l:=s)
      exact j
  · intro x i
    rw[List.mem_insert_iff]
    by_cases k : x=v
    case pos =>
      apply Or.inl k
    case neg =>
      apply Or.inr
      exact (List.mem_erase_of_ne (a:=x) (b:=v) (l:=s) k).mpr i

/--Theorem: `List.insert v s ⊆ List.cons v s`-/
theorem List_insert_sub_cons
  (s:List α)
  (v:α)
: List.insert v s ⊆ List.cons v s
:=
  by
    intro x
    rw [List.mem_insert_iff]
    intro h
    cases h with
    | inl i => rw[i]; exact List.mem_cons_self
    | inr i => exact List.mem_cons_of_mem v i

/--Theorem: `List.cons v (s.erase v) ≈ List.insert v (s.erase v)`-/
theorem List_cons_erase_ext_equiv_List_insert_erase
  (s : List α)
  (v : α)
: List.cons v (s.erase v) ≈ List.insert v (s.erase v)
:= by
  apply And.intro
  · intro x i
    rw[List.mem_cons] at i
    cases i with
    | inl j =>
      rw [j]
      exact List.mem_insert_self
    | inr j =>
      apply List.subset_insert
      exact j
  · exact List_insert_sub_cons (α:=α) (s.erase v) v

/--Theorem: If list `s` has no duplicates then `v ∉ List.erase s v`.-/
theorem not_mem_erase_Nodup
  (s : List α)
  (v : α)
  (h : s.Nodup)
: v ∉ List.erase s v
:=
    match s with
    | List.nil =>
      by
        rw [List.erase_nil]
        exact List.not_mem_nil
    | List.cons v' s' =>
      by
        if i : v = v' then
          rw [i]
          rw [List.erase_cons_head]
          cases h with
          | cons h_not_in h_nodup_tail =>
            intro j
            exact (h_not_in v' j) rfl
        else
          unfold List.erase
          --The proof is complicated by `List.erase` using Booleans
          match h_bool : (v' == v) with
          | true =>
            have h_eq :  v=v' := by
              simp only [beq_iff_eq] at h_bool
              exact h_bool.symm
            contradiction
          | false =>
            simp only [List.mem_cons, not_or]
            exact ⟨i, not_mem_erase_Nodup s' v h.tail⟩

/--Theorem: Given lists `s = (x::s') ≈ t`, we have `s' ≈ t.erase x`.-/
theorem List_ext_equiv_preserved_through_tail_and_erase
  (x:α)
  (s' t:List α)
  (h:(x::s')≈ t)
  (i:(x::s').Nodup)
  (j:t.Nodup)
: s' ≈ (t.erase x)
:=
  by
  apply And.intro
  · intro y k
    have l : x ∉ s' := (List.nodup_cons.mp i).1
    have m : y≠ x := by intro n; rw[n] at k; exact (l k)
    have n : y ∈ t := h.1 (List.mem_cons.mpr (Or.inr k))
    exact (List.mem_erase_of_ne m).mpr n
  · intro y k
    have l : y ≠ x := by intro m; rw [m] at k; exact ((not_mem_erase_Nodup (α:=α) t x j) k)
    have m : y ∈ t := List.erase_subset k
    have n : y ∈ (x::s') := h.2 m
    exact List.mem_of_ne_of_mem l n

/--Theorem: If `s ≈ t` and `s`, `t` have no duplicates, then `s`, `t` have the same length.-/
theorem Nodup_ext_equiv_preserves_length
  {s t : List α}
  (h : s ≈ t)
  (i : s.Nodup)
  (j : t.Nodup)
: s.length = t.length
:=
  by
  match s, t with
  | List.nil, List.nil => rfl
  | List.nil, List.cons y t' => exact ((List_nil_not_ext_equiv_non_nil (α:=α) (List.cons_ne_nil (α:=α) y t')) h.symm).elim
  | List.cons x s', List.nil => exact ((List_nil_not_ext_equiv_non_nil (α:=α) (List.cons_ne_nil (α:=α) x s')) h).elim
  | List.cons x s', List.cons y t' =>
    have k : s'.Nodup := (List.nodup_cons.mp i).2
    have l : ((y::t').erase x).Nodup := List.Nodup.erase x j
    have m : s' ≈ (y::t').erase x := List_ext_equiv_preserved_through_tail_and_erase (α:=α) x s' (y::t') h i j
    have n : s'.length = ((y::t').erase x).length := Nodup_ext_equiv_preserves_length m k l
    have o : (x::s').length = s'.length + 1 := by simp
    have oo : x ∈ (y::t') := h.1 List.mem_cons_self
    have p : (y::t').length = ((y::t').erase x).length + 1 := (List.length_erase_add_one oo).symm
    have q : (x::s').length = ((y::t').erase x).length + 1 := by rw[n] at o; exact o
    exact Eq.trans q p.symm

/--Theorem: `List.cons` preserves length equality.-/
theorem cons_preserves_length_equality {β : Type u'} (x : α) (σ : List α) (y : β) (τ : List β) (h : σ.length = τ.length)
: (x::σ).length = (y::τ).length
:= by
     have i : (x::σ).length = σ.length + 1 := rfl
     have j : (y::τ).length = τ.length + 1 := rfl
     rw [i, j, h]

/--Theorem: If `v ∈ s`, then `List.cons v (s.erase v) ≈ s`.-/
theorem List_cons_erase
  (s : List α)
  (v : α)
  (h : v ∈ s)
: (v :: s.erase v) ≈ s
:= Setoid.trans (List_cons_erase_ext_equiv_List_insert_erase α s v) (List_insert_erase α s v h)

/--Theorem: If list `t ⊆ (x::s)` but `x ∉ t` then `t ⊆ s`.-/
theorem List_sub_cons_sub_tail (t s : List α) (x : α) (h : t ⊆ (x::s)) (i : x ∉ t)
: t ⊆ s
:=
  by
  intro y
  intro j
  have k : y ∈ (x::s) := h j
  rw [List.mem_cons] at k
  cases k with
  | inl l => rw [l] at j; contradiction
  | inr l => exact l

/--Theorem: For lists `s`, `t`, if `t ⊆ (x::s)` and `t` has no duplicates, then `(t.erase x) ⊆ s`.-/
theorem List_sub_cons_erase_sub_tail (t s : List α) (x : α) (h : t ⊆ (x::s)) (ht : t.Nodup)
: (t.erase x) ⊆ s
:=
  by
  intro y i
  have j : y ∈ (x::s) := h (List.erase_subset i)
  simp [List.mem_cons] at j
  cases j with
  | inl k =>
    rw [k] at i
    exact ((not_mem_erase_Nodup (α := α) t x ht) i).elim
  | inr k => exact k

/--Theorem:If lists `s`, `t` have the same length, then `(x::s)`, `(y::t)` have the same length.-/
theorem List_lengths_equal_implies_cons_lengths_equal {β : Type u'} (s : List α) (x : α) (t : List β) (y : β)
(h : s.length = t.length)
: (x::s).length = (y::t).length
:=
  by
    unfold List.length
    rw [h]

/--Theorem: If lists `(x::s)` and `(y::t)` have the same length then
`s`, `t` have the same length.-/
theorem List_lengths_equal_implies_tail_lengths_equal
  {β : Type u'} (s : List α) (x : α) (t : List β)
(y:β) (h:(x::s).length = (y::t).length)
: s.length = t.length
:=
  by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    exact h

/--Theorem: Lists `s`, `t` have equal lengths iff `(x::s)`, `(y::t)` have equal lengths.-/
theorem List_length_agree_iff_cons_length_agree {β:Type u'} (s:List α) (x:α) (t:List β) (y:β)
: (s.length = t.length) ↔ (x::s).length = (y::t).length
:=
  by
    apply Iff.intro
    · intro h
      exact List_lengths_equal_implies_cons_lengths_equal (α:=α) (β:=β) s x t y h
    · intro h
      exact List_lengths_equal_implies_tail_lengths_equal (α:=α) (β:=β) s x t y h

/--Theorem: The list `s` has length just the length of `(s.erase x) + 1`, assuming `x ∈ s`.-/
theorem List_length_erase_of_mem_plus_one (s:List α) (x:α) (h: x ∈ s)
: s.length = (s.erase x).length +1
:=
  by
    have i : (s.erase x).length = s.length -1
    := List.length_erase_of_mem (α:=α) (a:=x) (l:=s) h
    rw[i]
    match s with
    | List.nil => exact (List.not_mem_nil (a:=x) h).elim
    | List.cons y t => simp

/--Theorem: Given a list `s`, if `x ∈ s` and `(s.erase x) ≈ t` then `s ≈ (x::t)`.-/
theorem List_ext_equiv_preserved_adjoining
  (s t : List α)
  (x : α)
  (h : x∈ s)
  (j : s.erase x ≈ t)
: s ≈ (x::t)
:=
  by
  apply And.intro
  · intro y
    intro k
    if l : y = x then
      rw[l]
      apply List.mem_cons_self
    else
      have k : y ∈ (s.erase x) :=  (List.mem_erase_of_ne l).mpr k
      have l : y ∈ t := (List_mem_respects_ext_equiv (α:=α) (s.erase x) t j y).mp k
      exact List.mem_cons_of_mem (x:α) l
  · intro y
    if k : y = x then
      rw[k]
      intro
      exact h
    else
      intro l
      rw[List.mem_cons] at l
      cases l with
      | inl m => exact (k m).elim
      | inr m => exact List.erase_subset (j.2 m)

/-
structure keyvaluepair {α: Type u} {β : Type u'} where
  keys : List α
  values : List β
  hN : keys.Nodup
  hl : keys.length = values.length
-/

/-
def eval {α : Type u} {β : Type u'} (pair : keyvaluepair (α:=α) (β:=β)) (key : α) (key_in : key ∈ pair.keys)
: β
:=
  by
  cases pair.keys with
  | nil =>
    have : pair.keys.length = 0
    := by rfl

    have : pair.keys = ([] : List α)
    :=
      by
      cases pair.keys with
      | nil => rfl
      | cons x σ => exact List.cons_ne_nil

  | cons x σ =>
    have : key ∈ ([]:List α)
    :=
      by
      dsimp at key_in
      sorry
    sorry
-/

/--A structure of type `filter_result` is the output of a process used to restrict a pair `(σ,τ)` of lists `σ`, `τ` (which will be thought of as giving key-value pairs)
to a certain subset `old_keys` of the original list `σ` of keys. (The lists `σ`, `τ` do not appear here, however. The key-value pairs are evaluated according to index.)

Fields:\
  `keys`: the list of keys output by the filtering process; we will have `keys ≈ old_keys`; `old_keys` is an input to the process.\
  `hNodup`: a proof that `keys` has no duplicates.\
  `hkeys_equiv`: a proof that `old_keys ≈ keys`.\
  `values`: the list of values output by the filtering process.\
  `hlength`: a proof that `old_keys` and `values` have the same length (note that `old_keys` has no duplicates, proven by input `h_old_keys`).
-/
structure filter_result {α: Type u} {β : Type u'} (old_keys:List α) (h_old_keys : old_keys.Nodup) where
  keys : List α
  hNodup : keys.Nodup
  hkeys_equiv : ext_equiv α old_keys keys
  values : List β
  hlength : old_keys.length = values.length


/--Definition: `filter_values_in_position` converts a key-value pair `(s, t)` of lists `s, t`, and a list `s' ⊆ s`, where `s` has no duplicates,
into a key-value pair `(s'', t'')`, such that `s' ≈ s''` and `(s'',t'')` evaluates just as the restricion of `(s,t)` to `s'`.
(It is used when restricting an `assignment` of free variables of a formula of form `φ ∧ ψ` to the free variables of `φ` or of `ψ`.)
The definition also demands that `s`, `s'` are injective (i.e., `s.Nodup` and `s'.Nodup`;
it also demands that `s, t` have the same lengths, in order that `(s,t)` is a key-value pair.
The formal output of the function is a `filter_result` structure, with `old_keys = s'`.
-/
def filter_values_in_position
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s' ⊆ s)
  (t : List β)
  (hlength : s.length = t.length)
: filter_result (α:=α) (β:=β) s' hs'Nodup
:=
  match s with
  --Case: `s = []`:
  | List.nil =>
    --`s'`, `t` are also empty, so things are quite simple.
    have h : s' = ([] : List α) := by
      match s' with
      | List.nil => rfl
      | List.cons x s'_tail =>
          have i : x ∈ (x::s'_tail) := List.mem_cons_self (a:=x) (l:=s'_tail)
          have j : x ∈ [] := s'_sub_s i
          contradiction
    have i : s'.length = 0 := by rw [h]; rfl
    have j : s' ≈ List.nil := by rw [h]
    --Output in the empty list case:
    filter_result.mk [] List.nodup_nil j [] i
  --Case: `s` is non-empty:
  | List.cons x s_tail =>
    --So `t` is non-empty also...
    match t with
    --Subcase: `t` is empty (to be ruled out):
    | List.nil => by
      have h : ([]:List β).length = 0 := rfl
      have i : (x::s_tail).length = s_tail.length + 1 := rfl
      rw [h,i] at hlength
      contradiction
    --Subcase: `t` is empty:
    | List.cons y t_tail =>
      --This is the main case. There are two main possibilities: `x ∈ s'` or `x ∉ s'`.
      if h : x ∈ s' then
        --This case (`x ∈ s'`) is where we need the main work. We call `filter_values_in_position` recursively on the tails:
        let sub_result :=
          (filter_values_in_position
            s_tail
            (s'.erase x)
            -- Proof of `s_tail.Nodup`:
            hsNodup.tail
            -- Proof of `(s'.erase x).Nodup`:
            (List.Nodup.erase x hs'Nodup)
            -- Proof of `(s'.erase x) ⊆ s_tail`:
            (List_sub_cons_erase_sub_tail (α:=α) s' s_tail x s'_sub_s hs'Nodup)
            t_tail
            -- Proof of `s_tail.length = t_tail.length`
            (List_lengths_equal_implies_tail_lengths_equal (α:=α) (β:=β) s_tail x t_tail y hlength))
        --We now use the output `sub_result` to construct the desired `filter_result` object:
        filter_result.mk
          (keys := x :: sub_result.keys)
          (hNodup :=
            --Need proof of `keys.Nodup`, i.e., `(x::sub_result.keys).Nodup`.
            --We have:
            -- `(s'.erase x) ≈ sub_result.keys`  -- Proof: `sub_result.hkeys_equiv`
            -- `s'.Nodup`                        -- Proof: `hs'Nodup`
            -- `x ∈ s'`                          -- Proof: `h`
            -- `v ∉ List.erase s v`              -- Proof: `not_mem_erase_Nodup (s : List α) (v : α) (h : s.Nodup)`
            -- `x ∉ (s'.erase x)`                -- Proof: application of `not_mem_erase_Nodup`
            -- `x∉ sub_result.keys`              -- Proof: application of `List_non_mem_respects_ext_equiv`, with `(s'.erase x) ≈ sub_result.keys`
            -- `(x::sub_result.keys).Nodup`      -- Proof: application of `List.Nodup.cons`, using `x ∉ sub_result.keys` and `sub_result.keys.Nodup`
            List.Nodup.cons
              (List_non_mem_respects_ext_equiv
                (α:=α)
                (s'.erase x)
                (sub_result.keys)
                sub_result.hkeys_equiv
                x
                (not_mem_erase_Nodup (α:=α) s' x hs'Nodup : x ∉ (s'.erase x))
              )
              (sub_result.hNodup : sub_result.keys.Nodup)
          )
          (hkeys_equiv :=
            --Need proof of `ext_equiv α old_keys keys`, i.e., `ext_equiv α s' (x::sub_result.keys)`
            --We have:
            -- `(s'.erase x) ≈ sub_result.keys`   -- Proof: `sub_result.hkeys_equiv`
            -- `x ∈ s'`                           -- Proof: `h`
            --
            --So need proof of `s' ≈ (x :: sub_result.keys)`
            --But application of `List_ext_equiv_preserved_adjoining` gives that.
            (List_ext_equiv_preserved_adjoining
              (α:=α)
              s'
              sub_result.keys
              x
              (h : x∈ s')
              (sub_result.hkeys_equiv : (s'.erase x) ≈ sub_result.keys)
              : s' ≈ (x::sub_result.keys)))
          (values := y::sub_result.values)
          (hlength :=
            -- Need proof of `s'.length = (y::sub_result.values).length`; see explanation below.
            Eq.trans
            (sub_result.hlength ▸ List_length_erase_of_mem_plus_one (α:=α) s' x h)
            (List.length_cons (α:=β) (a:=y) (as:=sub_result.values)).symm)
            -- (1) `List_length_erase_of_mem_plus_one` returns proof of
            --   `s'.length = (s'.erase x).length + 1`
            --
            -- (2) `sub_result.hlength` returns a proof of
            --   `(s'.erase x).length = sub_result.values.length`
            --
            -- (3) The substitution of (2) in (1) yields a proof of
            --   `s'.length = sub_result.values.length + 1`
            --
            -- (4) `List.length_cons` returns a proof of
            --   `(y::sub_result.values).length = sub_result.values.length + 1`
            --
            -- (5) So applying `symm` to (4) yields a proof of
            --   `sub_result.values.length + 1 = (y::sub_result.values).length`
            --
            -- (6) So chaining (3) and (5) with transitivity yields a proof of
            --   `s'.length = (y::sub_result.values).length`,
            --
            -- as desired.
            --
      else  --Case `x ∉ s'`. Here we can just chop the heads of `s`, `t`, and carry on,
            --just providing some slight modifications to the proofs to pass for the
            --recursive call.
        filter_values_in_position
          s_tail
          s'
          hsNodup.tail
          hs'Nodup
          (List_sub_cons_sub_tail (α:=α) s' s_tail x s'_sub_s h)
          t_tail
          (List_lengths_equal_implies_tail_lengths_equal (α:=α) (β:=β) s_tail x t_tail y hlength)

theorem filter_values_in_position_just_chops_heads_when_keys_head_not_in_subset
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s' ⊆ s)
  (t : List β)
  (hlength : s.length = t.length)
  (v : α)
  (s_tail : List α)
  (s_eq_cons_of : s = (v::s_tail))
  (y : β)
  (t_tail : List β)
  (t_eq_cons_of : t = (y::t_tail))
  (v_not_in_s' : v ∉ s')
  (hs_tailNodup : s_tail.Nodup
    := ((List.nodup_cons (a := v) (l := s_tail)).mp (s_eq_cons_of ▸ hsNodup)).2)
  (s'_sub_s_tail : s' ⊆ s_tail
    := List_sub_cons_sub_tail α s' s_tail v (s_eq_cons_of.symm ▸ s'_sub_s) v_not_in_s')
  (hlength_tail : s_tail.length = t_tail.length
    :=
      List_lengths_equal_implies_tail_lengths_equal
        α s_tail v t_tail y (s_eq_cons_of.symm ▸ (t_eq_cons_of.symm ▸ hlength)))
: (filter_values_in_position α s s' hsNodup hs'Nodup s'_sub_s t hlength)
 = (filter_values_in_position α s_tail s' hs_tailNodup hs'Nodup s'_sub_s_tail t_tail hlength_tail)
:=by
  conv_lhs => unfold filter_values_in_position
  split  --splitting s
  · next => --Case s = [] (leads to contradiction)
    exact ((List.cons_ne_nil v s_tail) s_eq_cons_of.symm).elim
  · next v_1 s_tail_1 _ _ _ => --Case s = x :: tail
    injection s_eq_cons_of.symm with v_1_eq_v s_tail_1_eq_s_tail
    subst v_1_eq_v s_tail_1_eq_s_tail
    split --splitting t
    · next => --Case t = [], which is contradiction in general here
        contradiction
    · next y_1 t_tail_1 _ _ => --Case t = (y_1 :: t_tail_1)
        injection t_eq_cons_of.symm with y_1_eq_y t_tail_1_eq_t_tail
        subst y_1_eq_y t_tail_1_eq_t_tail
        split
        · next v_in_s' =>-- Case v ∈ s'  (leads to contradiction)
          exact (v_not_in_s' v_in_s').elim
        · next _ => --Case v ∉ s'
          rfl

def value_at_index
  {β : Type u}
  (τ : List β)
  (index : Nat)
  (hindex : index < τ.length)
: β
:=
  match τ with
  | List.nil =>
    by
    rw [List.length_nil] at hindex
    exact (Nat.not_lt_zero index hindex ).elim
  | List.cons y  τ' =>
    match index with
    | Nat.zero => y
    | Nat.succ n =>
      have n_lt_τ'_length : n < τ'.length
      :=
        by
        have τ_length : (y::τ').length = τ'.length + 1
        := List.length_cons
        have succ_lengths_lt : n+1 < τ'.length + 1
        :=
          by
          rw [← τ_length]
          exact hindex
        exact Nat.lt_of_succ_lt_succ succ_lengths_lt
      value_at_index τ' n n_lt_τ'_length

theorem filter_keys_index_of_item_in_subset_lt_filter_values_length
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s' ⊆ s)
  (t : List β)
  (hlength : s.length = t.length)
  (v : α)
  (hv : v ∈ s')
: ((filter_values_in_position α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength).keys.idxOf v) <
  (filter_values_in_position α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength).values.length
:= sorry

theorem list_index_of_item_in_subset_lt_list_length
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s' ⊆ s)
  (v : α)
  (hv : v ∈ s')
: s.idxOf v < s.length
:= s.idxOf_lt_length_of_mem (s'_sub_s hv)

theorem filter_values_in_position_values_neq_nil_when_some_element_in_subset
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s'⊆ s)
  (t : List β)
  (hlength : s.length = t.length)
  (v : α)
  (hvs' : v ∈ s')
: (filter_values_in_position α s s' hsNodup hs'Nodup s'_sub_s t hlength).values ≠ []
:= sorry

theorem filter_values_in_position_values_head_is_t_head_when_original_keys_head_in_old_keys
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s' ⊆ s)
  (t : List β)
  (hlength : s.length = t.length)
  (v : α)
  (hvs' : v ∈ s')
  (s_tail : List α)
  (hvs_tail : s = (v::s_tail))
  (y : β)
  (t_tail : List β)
  (hyt_tail : t = (y::t_tail))
: ∃ (t'_tail : List β), (filter_values_in_position α s s' hsNodup hs'Nodup s'_sub_s t hlength).values = (y::t'_tail)
:= sorry

theorem filter_values_in_position_superset_keys_head_in_subset_makes_it_keys_head
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s'⊆ s)
  (t : List β)
  (hlength : s.length = t.length)
  (v : α)
  (hv : v ∈ s')
  (s_tail : List α)
  (hvs_tail : s = (v::s_tail))
: ∃ (s'_tail : List α), (filter_values_in_position α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength).keys = (v::s'_tail)
:= sorry

theorem filter_values_in_position_preserves_value_at_input
  {β : Type u'}
  (s s' : List α)
  (hsNodup : s.Nodup)
  (hs'Nodup : s'.Nodup)
  (s'_sub_s : s'⊆ s)
  (t : List β)
  (hlength : s.length = t.length)
  (v : α)
  (hv : v ∈ s')
: value_at_index
    (filter_values_in_position α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength).values
    ((filter_values_in_position α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength).keys.idxOf v)
    (filter_keys_index_of_item_in_subset_lt_filter_values_length α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength v hv)
  = value_at_index t (s.idxOf v) (hlength.symm ▸ (list_index_of_item_in_subset_lt_list_length α (β := β) s s' hsNodup hs'Nodup s'_sub_s v hv))
:=
  sorry
/-
  by
  let fr := filter_values_in_position α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength
  have h_fr_eq_fvip : fr = filter_values_in_position α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength := rfl
  cases h_fr_eq_con : fr with
  | mk fr_keys  fr_hNodup  fr_hkeys_equiv fr_values fr_hlength =>
  have s'_equiv_keys : s' ≈ fr_keys
  := fr_hkeys_equiv
  have fr_keys_eq : fr_keys = fr.keys
  :=by simp only [h_fr_eq_con]
  have fr_values_eq : fr_values = fr.values
  :=by simp only [h_fr_eq_con]

  have v_in_keys : v ∈ fr_keys
  := s'_equiv_keys.1 hv
  have lh_keys_gt_0 : fr_keys.length > 0
  := List.length_pos_of_mem v_in_keys
  have v_in_s : v ∈ s
  := s'_sub_s hv
  have lh_s_gt_0 : s.length > 0
  := List.length_pos_of_mem v_in_s
  have s_not_nil : s ≠ []
  := List.ne_nil_of_length_pos lh_s_gt_0
  have keys_not_nil : fr_keys ≠ []
  := fun hyp => List.not_mem_nil (hyp ▸ v_in_keys)
  have lh_keys_eq_lh_old_keys : fr_keys.length = s'.length
  := Nodup_ext_equiv_preserves_length α s'_equiv_keys.symm fr_hNodup hs'Nodup
  have lh_values_eq_lh_keys : fr_values.length = fr_keys.length
  := lh_keys_eq_lh_old_keys ▸ fr_hlength.symm
  have lh_values_gt_0 : fr_values.length > 0
  := lh_values_eq_lh_keys ▸ lh_keys_gt_0
  have values_not_nil : fr_values ≠ []
  := List.ne_nil_of_length_pos lh_values_gt_0
  have fr_keys_idxOf_v_lt_length_fr_values : fr_keys.idxOf v < fr_values.length
  :=  (fr_values_eq.symm ▸ (fr_keys_eq.symm ▸ (filter_keys_index_of_item_in_subset_lt_filter_values_length α (β:=β) s s' hsNodup hs'Nodup s'_sub_s t hlength v hv)))
  have fr_dot_keys_idxOf_v_lt_length_fr_dot_values : fr.keys.idxOf v < fr.values.length
  :=
    by
    rw[← fr_keys_eq]
    rw[← fr_values_eq]
    exact fr_keys_idxOf_v_lt_length_fr_values

  unfold value_at_index
  dsimp only
  --fr.keys
  --fr.values
  --fr.hNodup : keys.Nodup
  --fr.hkeys_equiv : ext_equiv α old_keys keys
  --fr.hlength : old_keys.length = values.length

  cases fr_values with
  | nil => exact (values_not_nil rfl).elim
  | cons y tail =>
    dsimp
    split
    · --Case: fr_values = [] (leads to contradiction)
      next heq hxhindex =>
        have fr_values_nil : fr.values = []
        := heq
        have cons_nil : y::tail = []
        :=
          by
          rw [h_fr_eq_con] at fr_values_nil
          dsimp at fr_values_nil
          exact fr_values_nil
        exact (values_not_nil cons_nil).elim
    · --Case: fr_values = (y^+::τ'^+)
      next fr_head fr_tail hyp1 hyp2 hyp3 =>
      split
      · --Case: fr_keys.idxOf v = 0
        next fr_keys_idxOf_v_eq_0 _ =>
          split --matching t
          · next =>
              --Case: t = [] (leads to contradiction)
              have lh_nil_gt_0 : ([]:List α).length > 0
              := hlength ▸ lh_s_gt_0
              have zero_lt_zero : 0 < 0
              := (List.length_nil) ▸ lh_nil_gt_0
              exact ((Nat.lt_irrefl 0) zero_lt_zero).elim
          · next  t_head t_tail _ _ _ _ =>
              --Case : t = (y^{++} :: τ'^{++})
              split
              · next keys_idxOf_v_eq_zero _ _ _ _ s_idxOf_v_eq_zero _ =>
                  --Case: s.index v = 0 (that is, s = (v::...), since s.length > 0)
                  cases s with
                  | nil => exact (s_not_nil rfl).elim
                  | cons w s_tail =>
                    have w_eq_v : w = v
                    :=
                      by
                      cases Decidable.em (w=v) with
                      | inl hypwv => exact hypwv
                      | inr hypwv =>
                        have zero_eq_succ : 0 = (s_tail.idxOf v).succ
                        := Eq.trans s_idxOf_v_eq_zero.symm  (List.idxOf_cons_ne s_tail hypwv)
                        exact (Nat.succ_ne_zero (s_tail.idxOf v) zero_eq_succ.symm).elim
                    subst w_eq_v
                    let filter_hyp :=
                      filter_values_in_position_values_head_is_t_head_when_original_keys_head_in_old_keys
                        α (w::s_tail) s' hsNodup hs'Nodup s'_sub_s (t_head::t_tail) hlength w hv s_tail (Eq.refl (w::s_tail)) t_head t_tail (Eq.refl (t_head::t_tail))
                    cases filter_hyp with
                    | intro t'_tail filter_hyp' =>
                    have join : fr_head::fr_tail = t_head::t'_tail
                    := Eq.trans hyp2.symm filter_hyp'
                    injection join with join_head _
              · next n _ s_idxOf_v_succ _ =>--Case: s.index v > 0
                cases s with
                  | nil => exact (s_not_nil rfl).elim
                  | cons w s_tail =>
                    have v_neq_w : v ≠ w
                    :=by
                      intro v_eq_w
                      subst v_eq_w
                      rw [List.idxOf_cons_self] at s_idxOf_v_succ
                      exact ((Nat.succ_ne_zero n) s_idxOf_v_succ.symm).elim
                    have w_not_in_s' : w ∉ s'
                    :=by
                      intro w_in_s'
                      let filter_hyp := filter_values_in_position_superset_keys_head_in_subset_makes_it_keys_head
                        α (w::s_tail) s' hsNodup hs'Nodup s'_sub_s (t_head::t_tail) hlength w w_in_s' s_tail (Eq.refl (w::s_tail))
                      cases filter_hyp with
                      | intro s'_tail filter_hyp' =>
                      have join : (w::s'_tail).idxOf v = 0
                      := filter_hyp'▸ fr_keys_idxOf_v_eq_0
                      have zero_eq_succ : 0 = (s'_tail.idxOf v).succ
                      := Eq.trans join.symm (List.idxOf_cons_ne s'_tail v_neq_w.symm)
                      exact Nat.succ_ne_zero (s'_tail.idxOf v) zero_eq_succ.symm
                    have hs_tailNodup : s_tail.Nodup
                    := (List.nodup_cons.mp hsNodup).2
                    have s'_sub_s_tail : s' ⊆ s_tail
                    := (List_sub_cons_sub_tail α s' s_tail w s'_sub_s w_not_in_s')
                    have hlength_tail : s_tail.length = t_tail.length
                    := (List_lengths_equal_implies_tail_lengths_equal α s_tail v t_tail t_head hlength)
                    have fr_eq_fvip_of_heads_chopped :
                      fr = filter_values_in_position α s_tail s' hs_tailNodup  hs'Nodup s'_sub_s_tail t_tail hlength_tail
                    := Eq.trans h_fr_eq_fvip (filter_values_in_position_just_chops_heads_when_keys_head_not_in_subset α (w::s_tail) s' hsNodup hs'Nodup s'_sub_s (t_head::t_tail) hlength w s_tail (Eq.refl (w::s_tail)) t_head t_tail (Eq.refl (t_head::t_tail)) w_not_in_s')
                    unfold fr at fr_eq_fvip_of_heads_chopped
                    let recursive_call := filter_values_in_position_preserves_value_at_input s_tail s' hs_tailNodup hs'Nodup s'_sub_s_tail t_tail hlength_tail v hv
                    have general : ∀ (a b : filter_result s' hs'Nodup), (hab : a=b) → (hva : a.keys.idxOf v < a.values.length) → (hvb : b.keys.idxOf v < b.values.length) → (value_at_index (β:=β) a.values (a.keys.idxOf v) hva) = (value_at_index (β:=β) b.values (b.keys.idxOf v) hvb)
                    := by
                      intro a b hab hva hvb
                      subst hab
                      rfl
                    have two_values_at_index : value_at_index (β:=β) ((filter_values_in_position α (β:=β) (w::s_tail) s' hsNodup hs'Nodup s'_sub_s (t_head::t_tail) hlength).values) ((filter_values_in_position α (β:=β) (w::s_tail) s' hsNodup hs'Nodup s'_sub_s (t_head::t_tail) hlength).keys.idxOf v) fr_dot_keys_idxOf_v_lt_length_fr_dot_values =
                      value_at_index (β:=β) (filter_values_in_position α s_tail s' hs_tailNodup  hs'Nodup s'_sub_s_tail t_tail hlength_tail).values ((filter_values_in_position α s_tail s' hs_tailNodup  hs'Nodup s'_sub_s_tail t_tail hlength_tail).keys.idxOf v) (list_index_of_item_in_subset_lt_list_length α (β := β) (filter_values_in_position α s_tail s' hs_tailNodup  hs'Nodup s'_sub_s_tail t_tail hlength_tail).keys s' hs_tailNodup hs'Nodup s'_sub_s_tail v hv)
                    := general (filter_values_in_position α (w :: s_tail) s' hsNodup hs'Nodup s'_sub_s (t_head :: t_tail) hlength)
                               (filter_values_in_position α s_tail s' hs_tailNodup  hs'Nodup s'_sub_s_tail t_tail hlength_tail)
                               fr_eq_fvip_of_heads_chopped
                               fr_dot_keys_idxOf_v_lt_length_fr_dot_values
                               sorry


                    fr_eq_fvip_of_heads_chopped ▸ recursive_call
                      by
                      convert recursive_call
                    sorry


--                    (fr_eq_fvip_of_heads_chopped ▸ filter_values_in_position_preserves_value_at_input s_tail s' hs_tailNodup hs'Nodup s'_sub_s_tail t_tail hlength_tail v hv)
 --                   #check (fr_keys_eq ▸
 --                   sorry
      · --Case: fr_keys.idxOf v = n+1
        next =>
          sorry
-/

theorem value_at_succ_index_of_cons
  {β : Type u}
  (τ : List β)
  (index : Nat)
  (hindex : index < τ.length)
  (x : β)
: value_at_index (x::τ) (index+1) ((Nat.add_lt_add_right hindex 1) : index + 1 < (x::τ).length)
  = value_at_index τ index hindex
:= by rfl

#check Nat.zero_lt_succ
theorem zero_lt_length_cons
  {β : Type u}
  (τ : List β)
  (x : β)
: 0 < (x::τ).length
:= Nat.zero_lt_succ τ.length

theorem value_at_new_index_of_cons
  {β : Type u}
  (τ : List β)
  (x : β)
: value_at_index (x::τ) 0 (zero_lt_length_cons τ x: 0 < (x::τ).length) = x
:= by rfl

end Lists
--Logic syntax

/--A `var` structure represents a variable for first-order logic. It is just a wrapper for `Nat`,
and the results from the "Lists" section will mostly be applied to `List var`.-/
structure var where
 id : Nat
deriving DecidableEq, Hashable, Repr

--attribute [match_pattern] var.mk

/--An `LSTF` object represents a formula of the language of set theory (LST).-/
inductive LSTF where
| atomic_mem : var → var → LSTF          --Atomic membership $v ∈ w$
| atomic_eq : var → var → LSTF           --Atomic equality $v = w$
| conj : LSTF → LSTF → LSTF              --Conjunction $φ ∧ ψ$
| neg : LSTF → LSTF                      --Negation $¬φ$
| ex : var → LSTF → LSTF                 --Existential quantifier $∃v φ$

--attribute [match_pattern] LSTF.atomic_mem LSTF.atomic_eq LSTF.conj LSTF.neg LSTF.ex

--We define the other conjunctives in terms of those used for the constructors

/--Disjunction ($ϕ ∨ ψ$) of formulas of the LST.-/
def LSTF.disj : LSTF → LSTF → LSTF :=
 fun (phi:LSTF) (psi:LSTF) => LSTF.neg (LSTF.conj (LSTF.neg phi) (LSTF.neg psi))

/--Implication ($ϕ ⇒ ψ$) of formulas of the LST.-/
def LSTF.imp : LSTF → LSTF → LSTF :=
 fun (phi:LSTF) (psi:LSTF) => LSTF.neg (LSTF.conj phi (LSTF.neg psi))

/--Iff ($ϕ ⇔ ψ$) of formulas of the LST.-/
def LSTF.iff : LSTF → LSTF → LSTF :=
 fun (phi:LSTF) (psi:LSTF) => LSTF.conj (LSTF.imp phi psi) (LSTF.imp psi phi)

/--Universal quantification ($∀ v ϕ$) of formulas of the LST.-/
def LSTF.all : var → LSTF → LSTF :=
 fun (v:var) (phi:LSTF) => LSTF.neg (LSTF.ex v (LSTF.neg phi))

/--`free_var φ` is a list of the free variables of a formula `φ : LSTF`.
The list is duplication-free (`(free_var φ).Nodup` holds) but comes in some order.
The primary object of interest is in fact the *set* of free variables,
so we will generally compare lists of free variables up to
extensional equivalence (`≈`), not equality.-/
def free_var (φ: LSTF)
: List var
:= match φ with
| (LSTF.atomic_mem v_1 v_2) => insert v_1 (insert v_2 ∅)
| (LSTF.atomic_eq v_1 v_2) => insert v_1 (insert v_2 ∅)
| LSTF.conj ψ ρ => (free_var ψ) ∪ (free_var ρ)
| LSTF.neg ψ => free_var ψ
| LSTF.ex v ψ => List.erase (free_var ψ)  v

/--Theorem: `free_var φ` is injective.-/
theorem free_var_Nodup (φ:LSTF)
: (free_var φ).Nodup
:= match φ with
| (LSTF.atomic_mem _ _) => List.Nodup.insert (List.Nodup.insert List.nodup_nil)
| (LSTF.atomic_eq _ _) => List.Nodup.insert (List.Nodup.insert List.nodup_nil)
| LSTF.conj ψ ρ => List.Nodup.union (free_var ψ) (free_var_Nodup ρ)
| LSTF.neg ψ => free_var_Nodup ψ
| LSTF.ex v ψ => List.Nodup.erase v (free_var_Nodup ψ)

/--Definition: `free_var-excluding φ v` is just a list of the free variables of
the formula `(φ: LSTF)`, excluding the variable `v`.-/
def free_var_excluding
 (φ:LSTF)
 (v:var)
 : List var
 := List.erase (free_var φ) v

/--Theorem: Definitional characterization of `free_var_excluding φ v`.-/
theorem free_var_excluding_is (φ:LSTF) (v:var)
  : free_var_excluding φ v = List.erase (free_var φ) v
  := rfl

/--Theorem: The excluded variable `v` is not an element of `free_var_excluding φ v`.-/
theorem excluded_var_notin_free_var_excluding (φ:LSTF) (v:var)
: v ∉ free_var_excluding φ v
:= by
  rw [free_var_excluding_is φ v]
  exact not_mem_erase_Nodup (α:=var) (free_var φ) v (free_var_Nodup φ)

/--Theorem: `free_var_excluding φ v` is injective.-/
theorem free_var_excluding_Nodup (φ:LSTF) (v:var)
: (free_var_excluding φ v).Nodup
:= (free_var_excluding_is φ v) ▸ (List.Nodup.erase v (free_var_Nodup φ))

/--Theorem: If `v ∈ free_var φ` then xcluding `v` from `free_var φ`, followed by re-adjoining `v` at the head (with `List.cons`), results
in a string `s ≈ free_var φ`.-/
theorem cons_free_var_excluding_ext_equiv_free_var
  (φ:LSTF)
  (v:var)
  (h: v ∈ free_var φ)
  : (v :: (free_var_excluding φ v)) ≈ free_var φ
  := (free_var_excluding_is φ v) ▸
     List_cons_erase var (free_var φ) v h

/--Theorem: If `v ∉ free_var φ` then `free_var_excluding φ v ≈ free_var φ`-/
theorem free_var_excluding_is_free_var_if_excluded_not_present
 (φ:LSTF)
 (v:var)
 (h: v ∉ free_var φ)
 : free_var_excluding φ v ≈ free_var φ
 := (List.erase_of_not_mem h) ▸ (Setoid.refl free_var φ)

/--A structure of type `LSTModel` represents a model of the language of set theory (LST).\
Fields:\
`univ`: The universe of the model.\
`eq`: The "equality" relation of the model.\
`mem`: The "membership" relation of the model.\
The relations `eq` and `mem` are just arbitrary binary relations on `univ`.
-/
structure LSTModel where
  univ : Type u
  eq : univ → univ → Prop
  mem : univ → univ → Prop

/--A structure of type `assignment M φ` represents an assignment of the free variables
of the formula `(φ : LSTF)` to elements of the universe of the model `M` of LST (that is, `(M : LSTModel)`).
The assignment is represented by a key-value pair of lists (`keys` and `values` below).
It also contains certain auxiliary information to ensure things are appropriate.\
Fields:\
`keys`: Some list of variables (type `List var`)\
`hNodup` : Proof that `keys` is injective\
`hfree_var` : Proof that `keys ≈ free_var φ`\
`values` : Some list of elements of `M.univ`\
`hvalues` : Proof that `keys` and `values` have the same lengths\
-/
structure assignment (M : LSTModel) (φ : LSTF)  where
  keys : List var
  hNodup : keys.Nodup
  hfree_var : keys ≈ free_var φ
  values : List M.univ
  hvalues : keys.length = values.length

/--Definition: `var_eval` evaluates the value of an `assignment` structure at a given
variable in its list of keys.-/
def var_eval
  {M : LSTModel}
  {φ : LSTF}
  (a : assignment M φ)
  (v : var)
  (h : v ∈ a.keys)
: M.univ
:=
  let idv := a.keys.idxOf v
  let idv_lt_length_keys : idv < a.keys.length := List.idxOf_lt_length_iff.mpr h
  let idv_lt_length_values : idv < a.values.length := (a.hvalues)▸ idv_lt_length_keys
  value_at_index a.values idv idv_lt_length_values

/--Theorem: Characterization of the definitional list giving the free variables of an atomic formula of LST
(in general for equality or membership, without actually mentioning the formula itself).
Intended as a lemma for `free_var_atomic_eq` and `free_var_atomic_mem`, which specialize it to the
two kinds of atomic formulas.-/
theorem free_var_atomic (v v':var) : insert v (insert v' ∅) ≈ [v',v]
  := by
    apply And.intro
    · intro x
      simp only [List.empty_eq, List.mem_cons, List.not_mem_nil, or_false]
      intro h
      have i : (x = v) ∨ (x ∈ insert v' (∅:List var)) := by
        apply List.mem_insert_iff.mp h
      cases i with
      | inl j => exact Or.inr j
      | inr j =>
        have k : (x=v') ∨ (x∈ (∅:List var)) := by
          apply List.mem_insert_iff.mp j
        cases k with
        | inl l => exact Or.inl l
        | inr l => exact (List.not_mem_nil l).elim
    · intro x
      simp only [List.empty_eq, List.mem_cons, List.not_mem_nil, or_false]
      intro h
      apply List.mem_insert_iff.mpr
      cases h with
      | inl i =>
        apply Or.inr
        apply List.mem_insert_iff.mpr
        rw [i]
        apply Or.inl
        rfl
      | inr i =>
        apply Or.inl
        exact i

/--Theorem: Characterization of the free variables of an atomic membership formula of LST,
up to equivalence `≈`:
the free variables of the formula $v ∈ v'$ is `free_var (LSTF.atomic_mem v v') ≈ [v', v]`. (The reversal of `v` and `v'` is not significant,
since `[v, v'] ≈ [v', v]`; it's just the way this was written.))-/
theorem free_var_atomic_mem (v v':var)
: free_var (LSTF.atomic_mem v v') ≈ [v', v]
:=
  by
  unfold free_var
  exact free_var_atomic v v'

/--Theorem: Characterization of the free variables of an atomic equality formula of LST,
up to equivalence `≈`:
the free variables of the formula $v = v'$ is `free_var (LSTF.atomic_eq v v') ≈ [v', v]`. (The reversal of `v` and `v'` is not significant,
since `[v, v'] ≈ [v', v]`; it's just the way this was written.))-/
theorem free_var_atomic_eq (v v': var)
: free_var (LSTF.atomic_eq v v') ≈ [v', v]
:=
  by
  unfold free_var
  exact free_var_atomic v v'

/--Lemma: Characterization of `free_var (LSTF.conj φ ψ)`, as the union
 `(free_var φ) ∪ (free_var ψ)`. Intended as lemma toward theorem `free_var_conj`.-/
theorem free_var_conj_is (φ ψ : LSTF)
: free_var (LSTF.conj φ ψ) = (free_var φ) ∪ (free_var ψ)
:= rfl

/--Theorem: Characterization of `free_var` of a conjunction $φ ∧ ψ$,
up to equivalence `≈`, as the (List-style) "union" of `free_var φ` and `free_var ψ`.-/
theorem free_var_conj (φ ψ : LSTF)
: free_var (LSTF.conj φ ψ) ≈ (free_var φ) ∪ (free_var ψ)
:= (free_var_conj_is φ ψ) ▸ Setoid.refl ((free_var φ)∪(free_var ψ))

/--Theorem: Characterization of `free_var LSTF.neg φ` as `free_var φ`.
(Intended as lemma toward theorem `free_var_neg`.)-/
theorem free_var_neg_is (φ : LSTF)
: free_var (LSTF.neg φ) = free_var φ
:= rfl

/--Theorem: Characterization of `free_var` of a negation $¬φ$,
up to equivalence `≈`, as just `free_var φ`.-/
theorem free_var_neg (φ : LSTF)
: free_var (LSTF.neg φ) ≈ free_var φ
:= (free_var_neg_is φ) ▸ Setoid.refl (free_var φ)

/--Theorem: Characterization of `free_var LSTF.ex v φ`,
as `(free_var φ).erase v`. Intended as lemma toward theorem `free_var_ex`.-/
theorem free_var_ex_is (v:var) (φ : LSTF)
: free_var (LSTF.ex v φ) = (free_var φ).erase v
:= rfl

/--Theorem: Characterization of `free_var` of existential formula $∃ v φ$,
up to equivalence `≈`, as `(free_var φ).erase v`.-/
theorem free_var_ex (v:var) (φ : LSTF)
: free_var (LSTF.ex v φ) ≈ (free_var φ).erase v
:= (free_var_ex_is v φ) ▸ Setoid.refl ((free_var φ).erase v)

theorem free_var_ex_subset_free_var (v : var) (φ : LSTF)
: free_var (LSTF.ex v φ) ⊆ free_var φ
:= by rw[free_var_ex_is v φ]; apply List.erase_subset

/--Theorem: `v ∈ [v, v']` (where `[v, v'] : List var`). Intended as lemma toward
theorems `first_in_free_var_atomic_eq` and `first_in_free_var_atomic_mem`.-/
theorem first_in_List (v v':var)
: v ∈ ([v, v']: List var)
:= by apply List.mem_cons_self

/--Theorem: `v' ∈ [v, v']` (where `[v, v'] : List var`). Intended as lemma toward
theorems `second_in_free_var_atomic_eq` and `second_in_free_var_atomic_mem`.-/
theorem second_in_List (v v':var)
: v' ∈ ([v, v']: List var)
:= by simp [List.mem_cons]

/--Theorem: `v` is an element of the free variables of the atomic formula $v = v'$.-/
theorem first_in_free_var_atomic_eq (v v' :var) : v ∈ free_var (LSTF.atomic_eq v v')
:=
  by
  have h : [v', v] ⊆ free_var (LSTF.atomic_mem v v') := (free_var_atomic_mem v v').2
  have i : v ∈ [v',v] := second_in_List v' v
  exact h i

/--Theorem: `v'` is an element of the free variables of the atomic formula $v = v'$.-/
theorem second_in_free_var_atomic_eq (v v' :var) : v' ∈ free_var (LSTF.atomic_eq v v')
:=
  by
  have h : [v', v] ⊆ free_var (LSTF.atomic_mem v v') := (free_var_atomic_mem v v').2
  have i : v' ∈ [v',v] := first_in_List v' v
  exact h i

/--Theorem: `v` is an element of the free variables of the atomic formula $v ∈ v'$.-/
theorem first_in_free_var_atomic_mem (v v' :var)
: v ∈ free_var (LSTF.atomic_mem v v')
:=
  by
  have h : [v', v] ⊆ free_var (LSTF.atomic_mem v v') := (free_var_atomic_mem v v').2
  have i : v ∈ [v',v] := second_in_List v' v
  exact h i

/--Theorem: `v'` is an element of the free variables of the atomic formula $v ∈ v'$.-/
theorem second_in_free_var_atomic_mem (v v' :var) : v' ∈ free_var (LSTF.atomic_mem v v')
:=
  by
  have h : [v', v] ⊆ free_var (LSTF.atomic_mem v v') := (free_var_atomic_mem v v').2
  have i : v' ∈ [v',v] := first_in_List v' v
  exact h i

/--Theorem: The list of free variables of formula $φ$ is (List-wise) $⊆$ the free variables of $φ ∧ ψ$.-/
theorem free_var_first_conjunct_sub_free_var_conjunction
  (φ ψ : LSTF)
: free_var φ ⊆ free_var (LSTF.conj φ ψ)
:= fun (v:var) (h : v ∈ free_var φ) => List.mem_union_left h (free_var ψ)

/--Theorem: The list of free variables of formula $ψ$ is (List-wise) $⊆$ the free variables of $φ ∧ ψ$.-/
theorem free_var_second_conjunct_sub_free_var_conjunction
  (φ ψ : LSTF)
: free_var ψ ⊆ free_var (LSTF.conj φ ψ)
:= fun (v:var) (h : v ∈ free_var ψ) => List.mem_union_right (free_var φ) h

/--Theorem: The `free_var` of $∃vφ$ is precisely `free_var φ`, when `v` is not free in `φ`.-/
theorem free_var_identical_when_quantified_var_not_present
  (v:var)
  (φ:LSTF)
  (h:v ∉ free_var φ)
: free_var (LSTF.ex v φ) = free_var φ
:= List.erase_of_not_mem h

/--Theorem: The `free_var` of $∃vφ$ is `≈ free_var φ`, when `v` is not free in `φ`.-/
theorem free_var_ext_equiv_when_quantified_var_not_present
  (v:var)
  (φ:LSTF)
  (h:v ∉ free_var φ)
: free_var (LSTF.ex v φ) ≈ free_var φ
:= (free_var_identical_when_quantified_var_not_present v φ h).symm ▸ Setoid.refl (free_var φ)

/--Theorem: `v` is not free in $∃vφ$.-/
theorem bound_var_not_free  (v:var) (φ:LSTF)
: v ∉ free_var (LSTF.ex v φ)
:=  not_mem_erase_Nodup (α:=var) (free_var φ) v (free_var_Nodup φ)

/--Theorem: `free_var φ` is equivalent to `(v :: free_var (∃vφ))`, assuming `v ∈ free_var φ`.
(The notation `free_var (∃vφ)` is only pseudo-code.)-/
theorem free_var_matrix_ext_equiv_cons_when_bound_var_present
  (v:var)
  (φ:LSTF)
  (h:v ∈ free_var φ)
: (free_var φ) ≈ (v::free_var (LSTF.ex v φ))
:= (List_cons_erase (α:=var) (free_var φ) v h).symm

theorem var_ne_bound_var_free_iff_free_in_matrix
  (v : var)
  (φ : LSTF)
  (w : var)
  (hwv : w ≠ v)
: w ∈ free_var (LSTF.ex v φ) ↔ w ∈ free_var φ
:=
  by
  rw [free_var_ex_is v φ]
  exact (List.mem_erase_of_ne (a:=w) (b:=v) (l:=free_var φ) hwv)

/--Definition: Given an assignment structure `ass` of type `assignment M (φ∧ψ)`,
we restrict `ass` to the free variables of `ψ`, outputing an assignment
structure of type `assignment M ψ`.\
Remark: We don't actually record a proof that the restriction process
is "faithful", i.e. that it  evaluates to the same values
on the relevant variables. That should probably just be directly incorporated.-/
def rest_assignment_to_second_conjunct
  {M:LSTModel}
  {φ ψ:LSTF}
  (ass:assignment M (LSTF.conj φ ψ))
: assignment M ψ
:=
  --To produce the desired output of type `assignment M ψ`,
  --we will first use a call to `filter_values_in_position` to compute the main objects needed
  --for the constructor of `assignment M ψ`.
  --We call `filter_values_in_position` with the 3 lists:
  --  `s = free_var (φ∧ψ)`   (this is pseudo-code)
  --  `s' = free_var ψ`
  --  `t = ass.values`
  --The other parameters passed to filter_values_in_position are (implicit: the basic types α, β and) the proofs that these objects satisfy the right conditions.
  let filtered := filter_values_in_position
    (α := var)
    (β := M.univ)
    --list `s`:
    (free_var (LSTF.conj φ ψ) : List var)
    --list `s'`:
    (free_var ψ : List var)
    --Proof of injectivity of `s`
    (free_var_Nodup (LSTF.conj φ ψ) : (free_var (LSTF.conj φ ψ)).Nodup)
    --Proof of injectivity of `s'`
    (free_var_Nodup ψ : (free_var ψ).Nodup)
    --Proof that `s ⊆ s'`
    (free_var_second_conjunct_sub_free_var_conjunction φ ψ:  (free_var ψ) ⊆ (free_var (LSTF.conj φ ψ)))
    --list `t`
    (ass.values : List M.univ)
    --proof that `s.length = t.length`; this isn't just ass.hvalues, since we didn't set s = ass.keys
    --But s.length = ass.keys.length = ass.values.length, so we use transitivity of = and proofs of these two equalities:
    (Eq.trans
      --proof that `s.length = ass.keys.length`
      (Nodup_ext_equiv_preserves_length
        (α:=var)
        ass.hfree_var -- proof that `ass.keys ≈ s`
        ass.hNodup --proof that `ass.keys.Nodup`
        (free_var_Nodup (LSTF.conj φ ψ)) -- proof that `s.Nodup`
      ).symm
      ass.hvalues
    : (free_var (LSTF.conj φ ψ)).length = ass.values.length)
  --With the data `filtered` returned from `filter_values_in_position`, we can easily construct the desired `assignment` object:
  assignment.mk
    (keys:=free_var ψ)
    (hNodup:=free_var_Nodup ψ)
    (hfree_var := Setoid.refl (free_var ψ))
    (values:=filtered.values)
    (hvalues:=filtered.hlength)

/--Definition: This is just the variant of `rest_assignment_to_second_conjunct`,
with φ replacing ψ in the obvious manner.-/
def rest_assignment_to_first_conjunct
  {M : LSTModel}
  {φ ψ : LSTF}
  (ass : assignment M (LSTF.conj φ ψ))
: assignment M φ
:=
  let filtered := filter_values_in_position
    (α := var)
    (β:= M.univ)
    (free_var (LSTF.conj φ ψ) : List var)
    (free_var φ : List var)
    (free_var_Nodup (LSTF.conj φ ψ) : (free_var (LSTF.conj φ ψ)).Nodup)
    (free_var_Nodup φ : (free_var φ).Nodup)
    (free_var_first_conjunct_sub_free_var_conjunction φ ψ
        :(free_var φ) ⊆ (free_var (LSTF.conj φ ψ)))
    (ass.values)
    (Eq.trans
      (Nodup_ext_equiv_preserves_length
        (α:=var)
        ass.hfree_var
        ass.hNodup
        (free_var_Nodup (LSTF.conj φ ψ))
      ).symm
      ass.hvalues
    : (free_var (LSTF.conj φ ψ)).length = ass.values.length)
  assignment.mk
    (keys:=free_var φ)
    (hNodup:=free_var_Nodup φ)
    (hfree_var := Setoid.refl (free_var φ))
    (values:=filtered.values)
    (hvalues:=filtered.hlength)

/--Definition: Converts a structure of type `assignment M ¬φ` to the corresponding
one of type `assignment M φ` (the key-value lists are unmodified).-/
def cast_assignment_to_nonnegation
  {M : LSTModel}
  {φ : LSTF}
  (ass : assignment M (LSTF.neg φ))
: assignment M φ
:=
  assignment.mk
    (keys:=ass.keys)
    (hNodup:=ass.hNodup)
    (hfree_var:=Setoid.trans ass.hfree_var (free_var_neg φ))
    (values:=ass.values)
    (hvalues:=ass.hvalues)

theorem cast_assignment_to_nonnegation_agrees
  {M : LSTModel}
  {φ : LSTF}
  (ass : assignment M (LSTF.neg φ))
  (v : var)
  (hv : v ∈ ass.keys)
  (hvnn : v ∈ (cast_assignment_to_nonnegation ass).keys)
: var_eval ass v hv = var_eval (cast_assignment_to_nonnegation ass) v hvnn
:= rfl

theorem rest_assignment_to_first_conjunct_agrees
  {M : LSTModel}
  {φ ψ : LSTF}
  (ass : assignment M (LSTF.conj φ ψ))
  (v : var)
  (hv : v ∈ ass.keys)
  (hvfc : v ∈ (rest_assignment_to_first_conjunct ass).keys)
: var_eval ass v hv = var_eval (rest_assignment_to_first_conjunct ass) v hvfc
:=
  by
  unfold var_eval
  dsimp only
  sorry

theorem rest_assignment_to_second_conjunct_agrees
  {M : LSTModel}
  {φ ψ : LSTF}
  (ass : assignment M (LSTF.conj φ ψ))
  (v : var)
  (hv : v ∈ ass.keys)
  (hvfc : v ∈ (rest_assignment_to_second_conjunct ass).keys)
: var_eval ass v hv = var_eval (rest_assignment_to_second_conjunct ass) v hvfc
:= sorry

--
--Quantifiers and assignments
--

def quantified_var_free_extend_assignment
  {M : LSTModel}
  {φ : LSTF}
  {v' : var}
  (ass : assignment M (LSTF.ex v' φ))
  (x : M.univ)
  (hv' : v' ∈ free_var φ)
: assignment M φ
:=  assignment.mk
      (keys:=(v'::ass.keys))
      (hNodup:=List.nodup_cons.mpr ⟨ass.hfree_var.1.mt (bound_var_not_free v' φ),ass.hNodup⟩)
      (hfree_var:=Setoid.trans
        (List_cons_respects_ext_equiv (α:=var) v' ass.hfree_var)
        (Setoid.symm (free_var_matrix_ext_equiv_cons_when_bound_var_present v' φ hv')))
      (values := (x::ass.values))
      (hvalues := List_lengths_equal_implies_cons_lengths_equal
                    (α:=var) (β:=M.univ) ass.keys v' ass.values x ass.hvalues)

def quantified_var_not_free_extend_assignment
  {M : LSTModel}
  {φ : LSTF}
  {v' : var}
  (ass : assignment M (LSTF.ex v' φ))
  (x : M.univ)
  (hv' : v' ∉ free_var φ)
: assignment M φ
:=  assignment.mk
      (keys := ass.keys)
      (hNodup := ass.hNodup)
      (hfree_var := Setoid.trans ass.hfree_var
                    (free_var_ext_equiv_when_quantified_var_not_present v' φ hv'))
      (values := ass.values)
      (hvalues := ass.hvalues)

/--Definition: Extends a structure of type `assignment M (∃vφ)`, together with an element `x ∈ M.univ`,
to an assignment `assignment M φ`, sending `v` to `x` if `v ∈ free_var φ` (and adjusting the relevant proofs).-/
def extend_assignment
  {M : LSTModel}
  {φ : LSTF}
  {v' : var}
  (ass : assignment M (LSTF.ex v' φ))
  (x : M.univ)
: assignment M φ
:=if h : v' ∈ free_var φ then (quantified_var_free_extend_assignment ass x h)
  else (quantified_var_not_free_extend_assignment ass x h)

theorem quantified_var_free_extend_assignment_equals
  {M : LSTModel}
  {φ : LSTF}
  {v' : var}
  (ass : assignment M (LSTF.ex v' φ))
  (x : M.univ)
  (hv' : v' ∈ free_var φ)
: extend_assignment ass x =  quantified_var_free_extend_assignment ass x hv'
:=by
  unfold extend_assignment
  simp only [hv', ↓reduceDIte]

theorem quantified_var_not_free_extend_assignment_equals
  {M : LSTModel}
  {φ : LSTF}
  {v' : var}
  (ass : assignment M (LSTF.ex v' φ))
  (x : M.univ)
  (hv' : v' ∉ free_var φ)
: extend_assignment ass x = quantified_var_not_free_extend_assignment ass x hv'
:=by
  unfold extend_assignment
  simp only [hv', ↓reduceDIte]

theorem quantified_var_free_var_in_extend_assignment_keys
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∈ free_var ψ)
: v ∈ (extend_assignment ass x).keys
:= (extend_assignment ass x).hfree_var.2 hv

theorem quantified_var_free_extend_assignment_keys
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∈ free_var ψ)
: (extend_assignment ass x).keys = (v::ass.keys)
:=by rw [quantified_var_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_not_free_extend_assignment_keys
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∉ free_var ψ)
: (extend_assignment ass x).keys = ass.keys
:=by rw [quantified_var_not_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_free_extend_assignment_values
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∈ free_var ψ)
: (extend_assignment ass x).values = (x::ass.values)
:=by rw [quantified_var_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_not_free_extend_assignment_values
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∉ free_var ψ)
: (extend_assignment ass x).values = ass.values
:=by rw [quantified_var_not_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_free_extend_assignment_keys_length
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∈ free_var ψ)
: (extend_assignment ass x).keys.length = ass.keys.length + 1
:=by rw [quantified_var_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_free_extend_assignment_values_length
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∈ free_var ψ)
: (extend_assignment ass x).values.length = ass.values.length + 1
:=by rw [quantified_var_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_not_free_extend_assignment_keys_length
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∉ free_var ψ)
: (extend_assignment ass x).keys.length = ass.keys.length
:=by rw [quantified_var_not_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_not_free_extend_assignment_values_length
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∉ free_var ψ)
: (extend_assignment ass x).values.length = ass.values.length
:=by rw [quantified_var_not_free_extend_assignment_equals ass x hv]; rfl

theorem quantified_var_free_index_var_in_extend_assignment_keys
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∈ free_var ψ)
: (extend_assignment ass x).keys.idxOf v = 0
:= by
   rw[quantified_var_free_extend_assignment_keys ass x hv]
   exact List.idxOf_cons_self

theorem extend_assignment_new_value
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
  (hv : v ∈ free_var ψ)
  (hvkeys : v ∈ (extend_assignment ass x).keys
    := quantified_var_free_var_in_extend_assignment_keys ass x hv)
: x = var_eval (extend_assignment ass x) v hvkeys
:=
  by
  unfold var_eval
  dsimp
  simp only [quantified_var_free_index_var_in_extend_assignment_keys ass x hv,
             quantified_var_free_extend_assignment_values ass x hv]
  rfl

theorem assignment_keys_subset_extend_assignment_keys
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (x : M.univ)
: ass.keys ⊆ (extend_assignment ass x).keys
:=by
  intro w hw
  have i : w ∈ free_var (LSTF.ex v ψ)
  := ass.hfree_var.1 hw
  have j : w ∈ free_var ψ
  := (free_var_ex_subset_free_var v ψ) i
  exact (extend_assignment ass x).hfree_var.2 j

theorem quantified_var_free_extend_assignment_agrees
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (hv : v ∈ free_var ψ)
  (w : var)
  (hw : w ∈ free_var (LSTF.ex v ψ))
  (x : M.univ)
  (hwmatrix : w ∈ (extend_assignment ass x).keys := assignment_keys_subset_extend_assignment_keys ass x (ass.hfree_var.2 hw))
: var_eval ass w (ass.hfree_var.2 hw) = var_eval (extend_assignment ass x) w hwmatrix
:=by
  unfold var_eval
  dsimp
  have ex_ass_keys_is : (extend_assignment ass x).keys = (v::ass.keys) := quantified_var_free_extend_assignment_keys ass x hv
  have ex_ass_values_is : (extend_assignment ass x).values = (x::ass.values) := quantified_var_free_extend_assignment_values ass x hv
  simp only [ex_ass_keys_is, ex_ass_values_is]
  have j : v ∉ free_var (LSTF.ex v ψ) := bound_var_not_free v ψ
  let idxvσ := (v::ass.keys).idxOf w
  have k : v ≠ w := by intro k; subst k; exact (j hw).elim
  let idxσ := ass.keys.idxOf w
  have l : idxσ < ass.keys.length := List.idxOf_lt_length_iff.mpr (ass.hfree_var.2 hw)
  have n : (v::ass.keys).idxOf w  = ass.keys.idxOf w + 1 := List.idxOf_cons_ne ass.keys k
  simp only [n]
  exact value_at_succ_index_of_cons ass.values (ass.keys.idxOf w) (ass.hvalues.symm ▸ l) x

theorem quantified_var_not_free_extend_assignment_agrees
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (hv : v ∉ free_var ψ)
  (w : var)
  (hw : w ∈ free_var (LSTF.ex v ψ))
  (x : M.univ)
  (hwmatrix : w ∈ (extend_assignment ass x).keys
    := assignment_keys_subset_extend_assignment_keys ass x (ass.hfree_var.2 hw))
: var_eval ass w (ass.hfree_var.2 hw) = var_eval (extend_assignment ass x) w hwmatrix
:=by
  unfold var_eval
  dsimp
  have ex_ass_keys_is : (extend_assignment ass x).keys = ass.keys
                          := quantified_var_not_free_extend_assignment_keys ass x hv
  have ex_ass_values_is : (extend_assignment ass x).values = ass.values
                            := quantified_var_not_free_extend_assignment_values ass x hv
  simp only [ex_ass_keys_is, ex_ass_values_is]

theorem extend_assignment_agrees
  {M : LSTModel}
  {ψ : LSTF}
  {v : var}
  (ass : assignment M (LSTF.ex v ψ))
  (w : var)
  (hw : w ∈ free_var (LSTF.ex v ψ))
  (x : M.univ)
  (hwmatrix : w ∈ (extend_assignment ass x).keys :=
    assignment_keys_subset_extend_assignment_keys ass x (ass.hfree_var.2 hw))
: var_eval ass w (ass.hfree_var.2 hw) = var_eval (extend_assignment ass x) w hwmatrix
:=if hv : v ∈ free_var ψ then quantified_var_free_extend_assignment_agrees ass hv w hw x hwmatrix
  else quantified_var_not_free_extend_assignment_agrees ass hv w hw x hwmatrix

/--Definition: the satisfaction relation for a model `M` of the language of set theory,
 formula `φ` of that language, and assignment `ass` for `M`, `φ`.-/
def sats (M:LSTModel) (φ:LSTF) (ass:assignment M φ) : Prop :=
match φ with
| LSTF.atomic_mem v v' =>
  M.mem (var_eval ass v (ass.hfree_var.2 (first_in_free_var_atomic_mem v v')))
        (var_eval ass v' (ass.hfree_var.2 (second_in_free_var_atomic_mem v v')))
| LSTF.atomic_eq v v' =>
  M.eq (var_eval ass v (ass.hfree_var.2 (first_in_free_var_atomic_eq v v')))
       (var_eval ass v' (ass.hfree_var.2 (second_in_free_var_atomic_eq v v')))
| LSTF.conj ψ ρ =>
  (sats M ψ (rest_assignment_to_first_conjunct ass))
  ∧ (sats M ρ (rest_assignment_to_second_conjunct ass))
| LSTF.neg ψ =>
  ¬ (sats M ψ (cast_assignment_to_nonnegation ass))
| LSTF.ex _ ψ =>
  ∃ x : M.univ,
    sats M ψ (extend_assignment ass x)

attribute [match_pattern]  sats

theorem sats_atomic_eq (M:LSTModel) (v v' : var) (ass : assignment M (LSTF.atomic_eq v v'))
: (sats M (LSTF.atomic_eq v v') ass) ↔
  (M.eq (var_eval ass v (ass.hfree_var.2 (first_in_free_var_atomic_mem v v')))
        (var_eval ass v' (ass.hfree_var.2 (second_in_free_var_atomic_mem v v'))))
:= by rfl

theorem sats_atomic_mem (M:LSTModel) (v v' : var) (ass : assignment M (LSTF.atomic_mem v v'))
: (sats M (LSTF.atomic_mem v v') ass) ↔
  (M.mem (var_eval ass v (ass.hfree_var.2 (first_in_free_var_atomic_mem v v')))
        (var_eval ass v' (ass.hfree_var.2 (second_in_free_var_atomic_mem v v'))))
:= by rfl

theorem sats_conj (M:LSTModel) (ψ ρ : LSTF) (ass : assignment M (LSTF.conj ψ ρ))
: (sats M (LSTF.conj ψ ρ) ass) ↔
  (sats M ψ (rest_assignment_to_first_conjunct ass))
  ∧ (sats M ρ (rest_assignment_to_second_conjunct ass))
:= by rfl

theorem sats_neg (M:LSTModel) (ψ : LSTF) (ass : assignment M (LSTF.neg ψ))
: (sats M (LSTF.neg ψ) ass) ↔
  ¬ (sats M ψ (cast_assignment_to_nonnegation ass))
:= by rfl

theorem sats_ex (M:LSTModel) (v : var) (ψ : LSTF) (ass : assignment M (LSTF.ex v ψ))
: (sats M (LSTF.ex v ψ) ass) ↔
  ∃ x : M.univ,
    sats M ψ (extend_assignment ass x)
:= by rfl


def respects {α : Type u} (eq : α → α → Prop) (mem : α → α → Prop)
: Prop
:= ∀ (c c' d d' : α), (eq c c') → (eq d d') → (mem c d) → (mem c' d')

structure StandardLSTModel where
  model : LSTModel
  heq : Equivalence model.eq
  hmem : respects model.eq model.mem


def equiv_ass (M : StandardLSTModel) (φ : LSTF) (ass ass' : assignment (M.model) φ)
: Prop
:= ∀ (v : var) (hv : v ∈ free_var φ), M.model.eq (var_eval ass v (ass.hfree_var.2 hv)) (var_eval ass' v (ass'.hfree_var.2 hv))

theorem equiv_ass_is_Equivalence (M : StandardLSTModel) (φ : LSTF)
: Equivalence (equiv_ass M φ)
where
  refl :=
    by
    intro ass v hv
    apply M.heq.refl
  symm :=
    by
    intro ass ass' hass v hv
    apply M.heq.symm
    exact hass v hv
  trans :=
    by
    intro ass1 ass2 ass3 h12 h23 v hv
    exact M.heq.trans (h12 v hv) (h23 v hv)

theorem equiv_ass_first_conjunct (M : StandardLSTModel) (φ ψ : LSTF) (ass ass' : assignment (M.model) (LSTF.conj φ ψ)) (hass : equiv_ass M (LSTF.conj φ ψ) ass ass')
: equiv_ass M φ (rest_assignment_to_first_conjunct ass) (rest_assignment_to_first_conjunct ass')
:=
  by
  unfold equiv_ass
  intro v hv
  have hvconj : v ∈ free_var (φ.conj ψ)
  := (free_var_first_conjunct_sub_free_var_conjunction φ ψ) hv
  let hassv := hass v hvconj
  have hvconjkeys : v ∈ ass.keys
  := ass.hfree_var.2 hvconj
  have hvkeys : v ∈ (rest_assignment_to_first_conjunct ass).keys
  := (rest_assignment_to_first_conjunct ass).hfree_var.2 hv
  have var_evals_agree : var_eval (rest_assignment_to_first_conjunct ass) v hvkeys = var_eval ass v hvconjkeys
  := (rest_assignment_to_first_conjunct_agrees ass v hvconjkeys hvkeys).symm
  have hvconjkeys' : v ∈ ass'.keys
  := ass'.hfree_var.2 hvconj
  have hvkeys' : v ∈ (rest_assignment_to_first_conjunct ass').keys
  := (rest_assignment_to_first_conjunct ass').hfree_var.2 hv
  have var_evals_agree' : var_eval (rest_assignment_to_first_conjunct ass') v hvkeys' = var_eval ass' v hvconjkeys'
  := (rest_assignment_to_first_conjunct_agrees ass' v hvconjkeys' hvkeys').symm
  exact (var_evals_agree'.symm ▸ (var_evals_agree.symm ▸ hassv))

theorem equiv_ass_second_conjunct (M : StandardLSTModel) (φ ψ : LSTF) (ass ass' : assignment (M.model) (LSTF.conj φ ψ)) (hass : equiv_ass M (LSTF.conj φ ψ) ass ass')
: equiv_ass M ψ (rest_assignment_to_second_conjunct ass) (rest_assignment_to_second_conjunct ass')
:=
  by
  unfold equiv_ass
  intro v hv
  have hvconj : v ∈ free_var (φ.conj ψ)
  := (free_var_second_conjunct_sub_free_var_conjunction φ ψ) hv
  let hassv := hass v hvconj
  have hvconjkeys : v ∈ ass.keys
  := ass.hfree_var.2 hvconj
  have hvkeys : v ∈ (rest_assignment_to_second_conjunct ass).keys
  := (rest_assignment_to_second_conjunct ass).hfree_var.2 hv
  have var_evals_agree : var_eval (rest_assignment_to_second_conjunct ass) v hvkeys = var_eval ass v hvconjkeys
  := (rest_assignment_to_second_conjunct_agrees ass v hvconjkeys hvkeys).symm
  have hvconjkeys' : v ∈ ass'.keys
  := ass'.hfree_var.2 hvconj
  have hvkeys' : v ∈ (rest_assignment_to_second_conjunct ass').keys
  := (rest_assignment_to_second_conjunct ass').hfree_var.2 hv
  have var_evals_agree' : var_eval (rest_assignment_to_second_conjunct ass') v hvkeys' = var_eval ass' v hvconjkeys'
  := (rest_assignment_to_second_conjunct_agrees ass' v hvconjkeys' hvkeys').symm
  exact (var_evals_agree'.symm ▸ (var_evals_agree.symm ▸ hassv))

theorem equiv_ass_neg (M : StandardLSTModel) (φ : LSTF) (ass ass' : assignment (M.model) (LSTF.neg φ)) (hass : equiv_ass M (LSTF.neg φ) ass ass')
: equiv_ass M φ (cast_assignment_to_nonnegation ass) (cast_assignment_to_nonnegation ass')
:=
  by
  unfold equiv_ass
  intro v hv
  have free_var_neg : free_var φ.neg = free_var φ := by rfl
  have hvneg : v ∈ free_var (LSTF.neg φ)
  := (free_var_neg ▸ hv)
  exact hass v hvneg --This didn't work so easily in the conjunction case

theorem equiv_ass_ex
  {M : StandardLSTModel}
  {ψ : LSTF}
  {v : var}
  (ass ass' : assignment (M.model) (LSTF.ex v ψ))
  (hass : equiv_ass M (LSTF.ex v ψ) ass ass')
  (x x' : M.model.univ) (hxx' : M.model.eq x x')
: equiv_ass M ψ (extend_assignment ass x) (extend_assignment ass' x')
:=
  by
  unfold equiv_ass
  intro w hw
  have hwkeys : w ∈ (extend_assignment ass x).keys
  := (extend_assignment ass x).hfree_var.2 hw
  have hwkeys' : w ∈ (extend_assignment ass' x').keys
  := (extend_assignment ass' x').hfree_var.2 hw
  cases Decidable.em (w=v) with
  | inl hwv =>
    subst hwv
    have var_eval_w : var_eval (extend_assignment ass x) w hwkeys = x
    := (extend_assignment_new_value ass x hw).symm
    have var_eval_w' : var_eval (extend_assignment ass' x') w hwkeys' = x'
    := (extend_assignment_new_value ass' x' hw).symm
    exact (var_eval_w'.symm ▸ (var_eval_w.symm ▸ hxx'))
  | inr hwv =>
    have hwex : w ∈ free_var (LSTF.ex v ψ)
    := (var_ne_bound_var_free_iff_free_in_matrix v ψ w hwv).mpr hw
    have hwexkeys : w ∈ ass.keys := ass.hfree_var.2 hwex
    have hwexkeys' : w ∈ ass'.keys := ass'.hfree_var.2 hwex
    have var_eval_w :
      var_eval (extend_assignment ass x) w hwkeys = var_eval ass w hwexkeys
    := (extend_assignment_agrees ass w hwex x hwkeys).symm
    have var_eval_w' :
      var_eval (extend_assignment ass' x') w hwkeys' = var_eval ass' w hwexkeys'
    := (extend_assignment_agrees ass' w hwex x' hwkeys').symm
    exact (var_eval_w'.symm ▸ (var_eval_w.symm ▸ hass w hwex))

theorem sats_respects_equiv
  (M : StandardLSTModel)
  (φ : LSTF)
: ∀ (ass ass' : assignment M.model φ)
    (hass : equiv_ass M φ ass ass')
    (hsats : sats M.model φ ass),
      (sats M.model φ ass')
:=
by
cases φ with
| atomic_eq v v' =>
  intro ass ass' hass hsats
  let v_in_free_var := first_in_free_var_atomic_eq v v'
  let v_in_ass_keys :=  (ass.hfree_var.2 v_in_free_var)
  let v_in_ass'_keys := (ass'.hfree_var.2 v_in_free_var)
  let v'_in_free_var := second_in_free_var_atomic_eq v v'
  let v'_in_ass_keys :=  (ass.hfree_var.2 v'_in_free_var)
  let v'_in_ass'_keys := (ass'.hfree_var.2 v'_in_free_var)
  let assv := (var_eval ass v v_in_ass_keys)
  let assv' := (var_eval ass v' v'_in_ass_keys )
  let ass'v := (var_eval ass' v v_in_ass'_keys)
  let ass'v' := (var_eval ass' v' v'_in_ass'_keys)
  have hassvv' : (M.model.eq assv assv') := (sats_atomic_eq M.model v v' ass).mp hsats
  have hassvass'v : (M.model.eq assv ass'v) := hass v v_in_free_var
  have hassv'ass'v' : (M.model.eq assv' ass'v') := hass v' v'_in_free_var
  exact (M.heq.trans (M.heq.trans (M.heq.symm hassvass'v) hassvv') hassv'ass'v')
| atomic_mem v v' =>
  intro ass ass' hass hsats
  let v_in_free_var := first_in_free_var_atomic_eq v v'
  let v_in_ass_keys :=  (ass.hfree_var.2 v_in_free_var)
  let v_in_ass'_keys := (ass'.hfree_var.2 v_in_free_var)
  let v'_in_free_var := second_in_free_var_atomic_eq v v'
  let v'_in_ass_keys :=  (ass.hfree_var.2 v'_in_free_var)
  let v'_in_ass'_keys := (ass'.hfree_var.2 v'_in_free_var)
  let assv := (var_eval ass v v_in_ass_keys)
  let assv' := (var_eval ass v' v'_in_ass_keys )
  let ass'v := (var_eval ass' v v_in_ass'_keys)
  let ass'v' := (var_eval ass' v' v'_in_ass'_keys)
  have hassvv' : (M.model.mem assv assv') := (sats_atomic_mem M.model v v' ass).mp hsats
  have hassvass'v : (M.model.eq assv ass'v) := hass v v_in_free_var
  have hassv'ass'v' : (M.model.eq assv' ass'v') := hass v' v'_in_free_var
  exact M.hmem assv ass'v assv' ass'v' hassvass'v hassv'ass'v' hassvv'
| conj ψ τ =>
  intro ass ass' hass hsats
  let ass1 := rest_assignment_to_first_conjunct ass
  let ass2 := rest_assignment_to_second_conjunct ass
  let ass'1 := rest_assignment_to_first_conjunct ass'
  let ass'2 := rest_assignment_to_second_conjunct ass'
  have hass1 : equiv_ass M ψ ass1 ass'1
  := equiv_ass_first_conjunct M ψ τ ass ass' hass
  have hass2 : equiv_ass M τ ass2 ass'2
  := equiv_ass_second_conjunct M ψ τ ass ass' hass
  apply And.intro
  · let hsats1 := hsats.1
    exact sats_respects_equiv M ψ ass1 ass'1 hass1 hsats1
  · let hsats2 := hsats.2
    exact sats_respects_equiv M τ ass2 ass'2 hass2 hsats2
| neg ψ =>
  intro ass ass' hass hsats
  let nonnegass := cast_assignment_to_nonnegation ass
  let nonnegass' := cast_assignment_to_nonnegation ass'
  have hnonnegass : equiv_ass M ψ nonnegass nonnegass'
  := equiv_ass_neg M ψ ass ass' hass
  have i : ¬ sats (M.model) ψ nonnegass'
  :=  by intro j; exact hsats (sats_respects_equiv M ψ nonnegass' nonnegass
                                ((equiv_ass_is_Equivalence M ψ).symm hnonnegass) j)
  exact i
| ex v ψ =>
  intro ass ass' hass hsats
  unfold sats at hsats
  cases hsats with
  | intro p satsmatrix =>
    use p
    let assp := extend_assignment ass p
    let ass'p := extend_assignment ass' p
    have i: equiv_ass M ψ assp ass'p
    := equiv_ass_ex ass ass' hass p p (M.heq.refl p)
    exact sats_respects_equiv M ψ assp ass'p i satsmatrix
