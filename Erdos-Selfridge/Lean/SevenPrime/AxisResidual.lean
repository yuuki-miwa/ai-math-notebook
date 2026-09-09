import SevenPrime.ConcreteCovering

/-!
# Concrete axis classes, disjointization, and residual clips

This module realizes the finite objects used in Lemmas 5.1 and 6.1.  An axis
family has one class `3^g p^f` for every positive exponent `f ≤ e`.  Its
`p`-coordinate slices are grouped by their 3-adic node and then clipped by the
sets already exposed at ancestor nodes.
-/

namespace SevenPrime

open scoped BigOperators

abbrev RootedBranch := Fin 2
abbrev RootedNode := Fin 2 × Fin 3
abbrev RootedLeaf := Fin 2 × Fin 3 × Fin 3

/-- One axis residue class with modulus `3^g p^f`, represented by its two CRT
coordinate residues. -/
structure AxisClassData (p g f : ℕ) where
  threeResidue : ZMod (3 ^ g)
  primeResidue : ZMod (p ^ f)

def AxisClassData.modulus {p g f : ℕ} (_ : AxisClassData p g f) : ℕ :=
  3 ^ g * p ^ f

/-- The data of the `e` axis classes `3^g p^f`, one for each `1 ≤ f ≤ e`. -/
structure AxisFamilyData (p e g : ℕ) where
  node : Fin e → ZMod (3 ^ g)
  residue : ∀ i : Fin e, ZMod (p ^ (i.val + 1))

def AxisFamilyData.axisClass {p e g : ℕ} (D : AxisFamilyData p e g)
    (i : Fin e) : AxisClassData p g (i.val + 1) :=
  ⟨D.node i, D.residue i⟩

@[simp] theorem AxisFamilyData.axisClass_modulus {p e g : ℕ}
    (D : AxisFamilyData p e g) (i : Fin e) :
    (D.axisClass i).modulus = 3 ^ g * p ^ (i.val + 1) := rfl

def AxisFamilyData.slice {p e g : ℕ} (D : AxisFamilyData p e g)
    (i : Fin e) : Set (ZMod (p ^ e)) :=
  primePowerSlice p e (i.val + 1) (Nat.succ_le_iff.mpr i.isLt) (D.residue i)

/-- The union of all `p`-slices assigned to a fixed 3-adic node. -/
def axisRawUnionAtNode {p e g : ℕ} (S : Set (ZMod (p ^ e)))
    (D : AxisFamilyData p e g) (v : ZMod (3 ^ g)) : Set (ZMod (p ^ e)) :=
  S ∩ Finset.univ.sup fun i => if D.node i = v then D.slice i else ∅

/-- Remove the `p`-mass already exposed along ancestors of `v`. -/
def axisDisjointizedAtNode {p e g : ℕ} (S : Set (ZMod (p ^ e)))
    (D : AxisFamilyData p e g) (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e)))
    (v : ZMod (3 ^ g)) : Set (ZMod (p ^ e)) :=
  axisRawUnionAtNode S D v \ ancestorExposed v

noncomputable def normalizedSetMass {X : Type*}
    (S U : Set X) : ℝ := (U.ncard : ℝ) / S.ncard

noncomputable def axisExposedMass {p e g : ℕ} (S : Set (ZMod (p ^ e)))
    (D : AxisFamilyData p e g) (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e)))
    (v : ZMod (3 ^ g)) : ℝ :=
  normalizedSetMass S (axisDisjointizedAtNode S D ancestorExposed v)

theorem axisDisjointizedAtNode_subset_raw {p e g : ℕ}
    (S : Set (ZMod (p ^ e))) (D : AxisFamilyData p e g)
    (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e)))
    (v : ZMod (3 ^ g)) :
    axisDisjointizedAtNode S D ancestorExposed v ⊆ axisRawUnionAtNode S D v :=
  Set.diff_subset

theorem axisExposedMass_nonneg {p e g : ℕ} (S : Set (ZMod (p ^ e)))
    (D : AxisFamilyData p e g) (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e)))
    (v : ZMod (3 ^ g)) :
    0 ≤ axisExposedMass S D ancestorExposed v := by
  unfold axisExposedMass normalizedSetMass
  positivity

private theorem axisRawUnionAtNode_ncard_le {p e g : ℕ}
    [NeZero (p ^ e)]
    (S : Set (ZMod (p ^ e))) (D : AxisFamilyData p e g)
    (v : ZMod (3 ^ g)) :
    (axisRawUnionAtNode S D v).ncard ≤
      ∑ i : Fin e, if D.node i = v then (D.slice i).ncard else 0 := by
  calc
    (axisRawUnionAtNode S D v).ncard ≤
        (Finset.univ.sup fun i : Fin e =>
          if D.node i = v then D.slice i else ∅).ncard :=
      Set.ncard_inter_le_ncard_right _ _
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin e)),
          (if D.node i = v then D.slice i else ∅).ncard :=
      ncard_finset_sup_le _ _
    _ = ∑ i : Fin e, if D.node i = v then (D.slice i).ncard else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp_all

/-- Concrete disjointization inequality: grouping by nodes and deleting
ancestor-exposed mass costs no more than the sum of the individual slices. -/
theorem axisDisjointization_ncard_le {p e g : ℕ} (hp : 0 < p)
    (S : Set (ZMod (p ^ e))) (D : AxisFamilyData p e g)
    (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e))) :
    ∑ v : ZMod (3 ^ g),
        (axisDisjointizedAtNode S D ancestorExposed v).ncard ≤
      ∑ i : Fin e, (D.slice i).ncard := by
  letI : NeZero (3 ^ g) := ⟨pow_ne_zero g (by norm_num)⟩
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e (Nat.ne_of_gt hp)⟩
  calc
    ∑ v : ZMod (3 ^ g),
        (axisDisjointizedAtNode S D ancestorExposed v).ncard ≤
      ∑ v : ZMod (3 ^ g), (axisRawUnionAtNode S D v).ncard := by
        apply Finset.sum_le_sum
        intro v hv
        exact Set.ncard_le_ncard (axisDisjointizedAtNode_subset_raw S D ancestorExposed v)
    _ ≤ ∑ v : ZMod (3 ^ g),
        ∑ i : Fin e, if D.node i = v then (D.slice i).ncard else 0 := by
      apply Finset.sum_le_sum
      intro v hv
      exact axisRawUnionAtNode_ncard_le S D v
    _ = ∑ i : Fin e, (D.slice i).ncard := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp

theorem axisDisjointization_slice_bound {p e g : ℕ} (hp : 0 < p)
    (S : Set (ZMod (p ^ e))) (D : AxisFamilyData p e g)
    (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e))) :
    ∑ v : ZMod (3 ^ g),
        (axisDisjointizedAtNode S D ancestorExposed v).ncard ≤
      ∑ i : Fin e, p ^ (e - (i.val + 1)) := by
  calc
    ∑ v : ZMod (3 ^ g),
        (axisDisjointizedAtNode S D ancestorExposed v).ncard ≤
      ∑ i : Fin e, (D.slice i).ncard :=
        axisDisjointization_ncard_le hp S D ancestorExposed
    _ = ∑ i : Fin e, p ^ (e - (i.val + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact primePowerSlice_ncard p e (i.val + 1) hp
        (Nat.succ_le_iff.mpr i.isLt) (D.residue i)

noncomputable def concreteAxisBudget (p e : ℕ) (S : Set (ZMod (p ^ e))) : ℝ :=
  (∑ i : Fin e, (p ^ (e - (i.val + 1)) : ℕ) : ℝ) / S.ncard

/-- Concrete form of Lemma 5.1 up to the finite tower budget: the exposed
variables are actual normalized cardinalities and their sum is bounded by the
sum of the individual prime-power slice capacities. -/
theorem lemma_5_1_concrete_levelwise_axis_budget {p e g : ℕ} (hp : 0 < p)
    (S : Set (ZMod (p ^ e))) (hS : 0 < S.ncard)
    (D : AxisFamilyData p e g)
    (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e))) :
    (∀ v, 0 ≤ axisExposedMass S D ancestorExposed v) ∧
      ∑ v : ZMod (3 ^ g), axisExposedMass S D ancestorExposed v ≤
        concreteAxisBudget p e S := by
  letI : NeZero (3 ^ g) := ⟨pow_ne_zero g (by norm_num)⟩
  constructor
  · exact fun v => axisExposedMass_nonneg S D ancestorExposed v
  · have hcard := axisDisjointization_slice_bound hp S D ancestorExposed
    have hcardReal :
        (∑ v : ZMod (3 ^ g),
          ((axisDisjointizedAtNode S D ancestorExposed v).ncard : ℝ)) ≤
        ∑ i : Fin e, ((p ^ (e - (i.val + 1)) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    simp_rw [axisExposedMass, normalizedSetMass]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hcardReal (by positivity)

/-! ## Concrete residual quantities on the `2 × 3 × 3` tree -/

def leafBranch (a : RootedLeaf) : RootedBranch := a.1
def leafNode (a : RootedLeaf) : RootedNode := (a.1, a.2.1)

/-- Disjointized axis masses indexed by the three levels of the live rooted
3-adic tree. -/
structure RootedAxisExposure where
  level1 : RootedBranch → ℝ
  level2 : RootedNode → ℝ
  level3 : RootedLeaf → ℝ

/-- The coordinate complement left along a leaf path.  Membership in
`promotedLevel3` selects whether the level-three block is part of the exact
skeleton (Stage II) or remains residual (Stage I). -/
def axisPathComplement
    {P : Type*} [Fintype P] [DecidableEq P]
    (promotedLevel3 : Finset P) (x : P → RootedAxisExposure)
    (p : P) (a : RootedLeaf) : ℝ :=
  1 - (x p).level1 (leafBranch a) - (x p).level2 (leafNode a) -
    (if p ∈ promotedLevel3 then (x p).level3 a else 0)

theorem axisPathComplement_nonneg
    {P : Type*} [Fintype P] [DecidableEq P]
    (promotedLevel3 : Finset P) (x : P → RootedAxisExposure)
    (hpath : ∀ p a,
      (x p).level1 (leafBranch a) + (x p).level2 (leafNode a) +
        (if p ∈ promotedLevel3 then (x p).level3 a else 0) ≤ 1) :
    ∀ p a, 0 ≤ axisPathComplement promotedLevel3 x p a := by
  intro p a
  unfold axisPathComplement
  linarith [hpath p a]

def SkeletonCovered {A P : Type*} [Fintype A] [Fintype P]
    (τ : A → ℝ) (q : P → A → ℝ) : ℝ :=
  ∑ a, τ a * (1 - ∏ p, q p a)

noncomputable def residualOutsideProduct
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (q : P → RootedLeaf → ℝ) (a : RootedLeaf) : ℝ :=
  ∏ p ∈ (Finset.univ.filter fun p => p ∉ T), q p a

noncomputable def residualSupportBudget
    {P : Type*} [Fintype P] [DecidableEq P]
    (β : P → ℝ) (T : Finset P) : ℝ :=
  ∏ p ∈ T, β p

/-- Positive exponent choices on every prime in a residual support. -/
abbrev SupportExponentVector {P : Type*} (T : Finset P) (e : P → ℕ) :=
  ∀ p : ↥T, Fin (e p)

noncomputable def exponentVectorCapacity
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (e : P → ℕ) (c : ∀ p, Fin (e p) → ℝ)
    (f : SupportExponentVector T e) : ℝ :=
  ∏ p : ↥T, c p (f p)

/-- The sum over all exponent vectors factorizes into the product of the
one-coordinate tower sums. -/
theorem exponentVectorCapacity_sum_eq_product
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (e : P → ℕ) (c : ∀ p, Fin (e p) → ℝ) :
    (∑ f : SupportExponentVector T e, exponentVectorCapacity T e c f) =
      ∏ p : ↥T, ∑ i, c p i := by
  exact (Fintype.prod_sum (fun p : ↥T => c p)).symm

theorem subtype_prod_eq_supportBudget
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (β : P → ℝ) :
    (∏ p : ↥T, β p) = residualSupportBudget β T := by
  change (∏ p ∈ T.attach, β p) = ∏ p ∈ T, β p
  exact Finset.prod_attach T β

/-- Concrete derivation of the residual coefficient bound
`Σ_(f_p) ∏_p c_p(f_p) ≤ B_T`. -/
theorem exponentVectorCapacity_sum_le_supportBudget
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (e : P → ℕ) (c : ∀ p, Fin (e p) → ℝ)
    (β : P → ℝ) (hc : ∀ p i, 0 ≤ c p i)
    (hbudget : ∀ p : ↥T, ∑ i, c p i ≤ β p) :
    (∑ f : SupportExponentVector T e, exponentVectorCapacity T e c f) ≤
      residualSupportBudget β T := by
  rw [exponentVectorCapacity_sum_eq_product, ← subtype_prod_eq_supportBudget]
  exact Finset.prod_le_prod (fun p hp => Finset.sum_nonneg fun i hi => hc p i)
    (fun p hp => hbudget p)

theorem exponentVectorCapacity_nonneg
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (e : P → ℕ) (c : ∀ p, Fin (e p) → ℝ)
    (hc : ∀ p i, 0 ≤ c p i) (f : SupportExponentVector T e) :
    0 ≤ exponentVectorCapacity T e c f := by
  exact Finset.prod_nonneg fun p hp => hc p (f p)

theorem residualSupportBudget_pos
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (β : P → ℝ) (hβ : ∀ p ∈ T, 0 < β p) :
    0 < residualSupportBudget β T := by
  exact Finset.prod_pos fun p hp => hβ p hp

noncomputable def residualL0 (τ R : RootedLeaf → ℝ) : ℝ :=
  ∑ a, τ a * R a

noncomputable def residualL1 (τ R : RootedLeaf → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b : RootedBranch =>
    ∑ a with leafBranch a = b, τ a * R a)

noncomputable def residualL2 (τ R : RootedLeaf → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun v : RootedNode =>
    ∑ a with leafNode a = v, τ a * R a)

noncomputable def residualL3 (τ R : RootedLeaf → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : RootedLeaf => τ a * R a)

/-- Unlike `L₃`, the tail clip deliberately maximizes over all leaves without
the profile weight, including leaves of zero `τ`-mass. -/
noncomputable def residualH (R : RootedLeaf → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty R

noncomputable def residualL0ForSupport
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) : ℝ :=
  residualL0 τ (residualOutsideProduct T q)

noncomputable def residualL1ForSupport
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) : ℝ :=
  residualL1 τ (residualOutsideProduct T q)

noncomputable def residualL2ForSupport
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) : ℝ :=
  residualL2 τ (residualOutsideProduct T q)

noncomputable def residualL3ForSupport
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) : ℝ :=
  residualL3 τ (residualOutsideProduct T q)

noncomputable def residualHForSupport
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (q : P → RootedLeaf → ℝ) : ℝ :=
  residualH (residualOutsideProduct T q)

theorem residualOutsideProduct_nonneg
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (q : P → RootedLeaf → ℝ)
    (hq : ∀ p a, 0 ≤ q p a) (a : RootedLeaf) :
    0 ≤ residualOutsideProduct T q a := by
  unfold residualOutsideProduct
  exact Finset.prod_nonneg fun p hp => hq p a

theorem residualL0_nonneg (τ R : RootedLeaf → ℝ)
    (hτ : ∀ a, 0 ≤ τ a) (hR : ∀ a, 0 ≤ R a) :
    0 ≤ residualL0 τ R := by
  exact Finset.sum_nonneg fun a ha => mul_nonneg (hτ a) (hR a)

theorem branchContribution_le_L1 (τ R : RootedLeaf → ℝ) (b : RootedBranch) :
    (∑ a with leafBranch a = b, τ a * R a) ≤ residualL1 τ R := by
  exact Finset.le_sup' (fun b : RootedBranch =>
    ∑ a with leafBranch a = b, τ a * R a) (Finset.mem_univ b)

theorem nodeContribution_le_L2 (τ R : RootedLeaf → ℝ) (v : RootedNode) :
    (∑ a with leafNode a = v, τ a * R a) ≤ residualL2 τ R := by
  exact Finset.le_sup' (fun v : RootedNode =>
    ∑ a with leafNode a = v, τ a * R a) (Finset.mem_univ v)

theorem leafContribution_le_L3 (τ R : RootedLeaf → ℝ) (a : RootedLeaf) :
    τ a * R a ≤ residualL3 τ R := by
  exact Finset.le_sup' (fun a : RootedLeaf => τ a * R a) (Finset.mem_univ a)

theorem residualValue_le_H (R : RootedLeaf → ℝ) (a : RootedLeaf) :
    R a ≤ residualH R := by
  exact Finset.le_sup' R (Finset.mem_univ a)

theorem residualL1_nonneg (τ R : RootedLeaf → ℝ)
    (hτ : ∀ a, 0 ≤ τ a) (hR : ∀ a, 0 ≤ R a) :
    0 ≤ residualL1 τ R := by
  let b : RootedBranch := 0
  calc
    0 ≤ ∑ a with leafBranch a = b, τ a * R a :=
      Finset.sum_nonneg fun a ha => mul_nonneg (hτ a) (hR a)
    _ ≤ residualL1 τ R := branchContribution_le_L1 τ R b

theorem residualL2_nonneg (τ R : RootedLeaf → ℝ)
    (hτ : ∀ a, 0 ≤ τ a) (hR : ∀ a, 0 ≤ R a) :
    0 ≤ residualL2 τ R := by
  let v : RootedNode := (0, 0)
  calc
    0 ≤ ∑ a with leafNode a = v, τ a * R a :=
      Finset.sum_nonneg fun a ha => mul_nonneg (hτ a) (hR a)
    _ ≤ residualL2 τ R := nodeContribution_le_L2 τ R v

theorem residualL3_nonneg (τ R : RootedLeaf → ℝ)
    (hτ : ∀ a, 0 ≤ τ a) (hR : ∀ a, 0 ≤ R a) :
    0 ≤ residualL3 τ R := by
  let a : RootedLeaf := (0, 0, 0)
  exact (mul_nonneg (hτ a) (hR a)).trans (leafContribution_le_L3 τ R a)

theorem residualH_nonneg (R : RootedLeaf → ℝ) (hR : ∀ a, 0 ≤ R a) :
    0 ≤ residualH R := by
  let a : RootedLeaf := (0, 0, 0)
  exact (hR a).trans (residualValue_le_H R a)

noncomputable def residualContribution0 {E : Type*} [Fintype E]
    (c : E → ℝ) (τ R : RootedLeaf → ℝ) : ℝ :=
  ∑ u, c u * residualL0 τ R

noncomputable def residualContribution1 {E : Type*} [Fintype E]
    (c : E → ℝ) (place : E → RootedBranch)
    (τ R : RootedLeaf → ℝ) : ℝ :=
  ∑ u, c u * ∑ a with leafBranch a = place u, τ a * R a

noncomputable def residualContribution2 {E : Type*} [Fintype E]
    (c : E → ℝ) (place : E → RootedNode)
    (τ R : RootedLeaf → ℝ) : ℝ :=
  ∑ u, c u * ∑ a with leafNode a = place u, τ a * R a

noncomputable def residualContribution3 {E : Type*} [Fintype E]
    (c : E → ℝ) (place : E → RootedLeaf)
    (τ R : RootedLeaf → ℝ) : ℝ :=
  ∑ u, c u * (τ (place u) * R (place u))

noncomputable def residualTailContribution {E : Type*} [Fintype E]
    (c : E → ℝ) (place : E → RootedLeaf) (R : RootedLeaf → ℝ) : ℝ :=
  ∑ u, c u * R (place u)

/-- A residual support is nonempty, and at level zero it must contain at least
two non-3 primes (singletons are pure towers already removed in Section 3). -/
def ResidualSupportAtLevel {P : Type*} [DecidableEq P]
    (T : Finset P) (g : ℕ) : Prop :=
  T.Nonempty ∧ (g = 0 → 2 ≤ T.card)

def nonemptySupports (P : Type*) [Fintype P] [DecidableEq P] :
    Finset (Finset P) :=
  (Finset.univ : Finset P).powerset.erase ∅

def multiPrimeSupports (P : Type*) [Fintype P] [DecidableEq P] :
    Finset (Finset P) :=
  (nonemptySupports P).filter fun T => 2 ≤ T.card

/-- The common Stage-I/Stage-II formula as a function of the concrete
per-prime path-complement blocks `q`.  Keeping this layer explicit makes the
separate convexity of every prime coordinate a theorem about the actual
functional rather than only about its individual summands. -/
noncomputable def clippedFunctionalFromQ
    {P : Type*} [Fintype P] [DecidableEq P]
    (promotedLevel3 : Finset P) (β : P → ℝ)
    (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) : ℝ :=
  SkeletonCovered τ q +
    ∑ T ∈ multiPrimeSupports P,
      residualSupportBudget β T *
        (residualL0ForSupport T τ q + residualL1ForSupport T τ q +
          residualL2ForSupport T τ q + residualL3ForSupport T τ q) +
    ∑ p ∈ (Finset.univ.filter fun p => p ∉ promotedLevel3),
      residualSupportBudget β {p} * residualL3ForSupport {p} τ q +
    ∑ T ∈ nonemptySupports P,
      residualSupportBudget β T / 27 * residualHForSupport T q

/-- The common Stage-I/Stage-II functional.  Level-one and level-two
singleton axes are always in the exact skeleton.  A singleton level-three
term is residual exactly when its prime is not in `promotedLevel3`. -/
noncomputable def clippedStageFunctional
    {P : Type*} [Fintype P] [DecidableEq P]
    (promotedLevel3 : Finset P) (β : P → ℝ)
    (τ : RootedLeaf → ℝ) (x : P → RootedAxisExposure) : ℝ :=
  clippedFunctionalFromQ promotedLevel3 β τ
    (axisPathComplement promotedLevel3 x)

noncomputable def stageIFunctional
    {P : Type*} [Fintype P] [DecidableEq P]
    (β : P → ℝ) (τ : RootedLeaf → ℝ) (x : P → RootedAxisExposure) : ℝ :=
  clippedStageFunctional ∅ β τ x

noncomputable def stageIIFunctional
    {P : Type*} [Fintype P] [DecidableEq P]
    (promotedLevel3 : Finset P) (β : P → ℝ)
    (τ : RootedLeaf → ℝ) (x : P → RootedAxisExposure) : ℝ :=
  clippedStageFunctional promotedLevel3 β τ x

def RootedProfilePolytope (τ : RootedLeaf → ℝ) : Prop :=
  (∀ a, 0 ≤ τ a ∧ τ a ≤ 2 / 27) ∧ ∑ a, τ a = 1

def AxisExposureFeasible
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) (β : P → ℝ) (x : P → RootedAxisExposure) : Prop :=
  ∀ p,
    (∀ b, 0 ≤ (x p).level1 b) ∧
    (∀ v, 0 ≤ (x p).level2 v) ∧
    (∀ a, 0 ≤ (x p).level3 a) ∧
    (∑ b, (x p).level1 b ≤ β p) ∧
    (∑ v, (x p).level2 v ≤ β p) ∧
    (∑ a, (x p).level3 a ≤ β p) ∧
    ∀ a,
      (x p).level1 (leafBranch a) + (x p).level2 (leafNode a) +
        (if p ∈ promoted then (x p).level3 a else 0) ≤ 1

structure ConcreteRelaxationPoint (P : Type*) where
  profile : RootedLeaf → ℝ
  axis : P → RootedAxisExposure

def concreteRelaxationDomain
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) (β : P → ℝ) : Set (ConcreteRelaxationPoint P) :=
  {z | RootedProfilePolytope z.profile ∧ AxisExposureFeasible promoted β z.axis}

noncomputable def concreteRelaxationValue
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) (β : P → ℝ) (z : ConcreteRelaxationPoint P) : ℝ :=
  clippedStageFunctional promoted β z.profile z.axis

theorem concreteRelaxationDomain_mono
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) {β β' : P → ℝ} (hβ : ∀ p, β p ≤ β' p) :
    concreteRelaxationDomain promoted β ⊆ concreteRelaxationDomain promoted β' := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro p
  obtain ⟨h1, h2, h3, hb1, hb2, hb3, hpath⟩ := hz.2 p
  exact ⟨h1, h2, h3, hb1.trans (hβ p), hb2.trans (hβ p),
    hb3.trans (hβ p), hpath⟩

noncomputable def finiteSupLinear {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty J] (w : J → I → ℝ) (x : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => ∑ i, x i * w j i)

theorem weightedSum_convexOn {I : Type*} [Fintype I]
    (w : I → ℝ) {s : Set (I → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun x => ∑ i, x i * w i) := by
  constructor
  · exact hs
  · intro x hx y hy a b ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem finiteSupLinear_convexOn {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty J] (w : J → I → ℝ) {s : Set (I → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (finiteSupLinear w) := by
  constructor
  · exact hs
  · intro x hx y hy a b ha hb hab
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro j hj
    calc
      (∑ i, (a • x + b • y) i * w j i) =
          a * (∑ i, x i * w j i) + b * (∑ i, y i * w j i) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ a * finiteSupLinear w x + b * finiteSupLinear w y := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun j => ∑ i, x i * w j i) (Finset.mem_univ j)) ha)
          (mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun j => ∑ i, y i * w j i) (Finset.mem_univ j)) hb)
      _ = a • finiteSupLinear w x + b • finiteSupLinear w y := by
        simp [smul_eq_mul]

theorem residualL1_convexOn (R : RootedLeaf → ℝ)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun τ => residualL1 τ R) := by
  let w : RootedBranch → RootedLeaf → ℝ :=
    fun b a => if leafBranch a = b then R a else 0
  convert finiteSupLinear_convexOn w hs using 1
  funext τ
  unfold residualL1 finiteSupLinear
  congr 1
  funext b
  simp [w, Finset.sum_filter]

theorem residualL2_convexOn (R : RootedLeaf → ℝ)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun τ => residualL2 τ R) := by
  let w : RootedNode → RootedLeaf → ℝ :=
    fun v a => if leafNode a = v then R a else 0
  convert finiteSupLinear_convexOn w hs using 1
  funext τ
  unfold residualL2 finiteSupLinear
  congr 1
  funext v
  simp [w, Finset.sum_filter]

theorem residualL3_convexOn (R : RootedLeaf → ℝ)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun τ => residualL3 τ R) := by
  let w : RootedLeaf → RootedLeaf → ℝ :=
    fun j a => if a = j then R a else 0
  convert finiteSupLinear_convexOn w hs using 1
  funext τ
  unfold residualL3 finiteSupLinear
  congr 1
  funext j
  simp [w]

/-! Convexity in a single concrete axis-complement block.  The coordinate
`z : RootedLeaf → ℝ` replaces one prime's path-complement values while all
other prime coordinates are held fixed. -/

theorem finset_prod_update_combo
    {P : Type*} [DecidableEq P] (s : Finset P) (q : P → ℝ) (p : P)
    (z₁ z₂ a b : ℝ) (hab : a + b = 1) :
    (∏ r ∈ s, Function.update q p (a * z₁ + b * z₂) r) =
      a * (∏ r ∈ s, Function.update q p z₁ r) +
        b * (∏ r ∈ s, Function.update q p z₂ r) := by
  by_cases hp : p ∈ s
  · rw [Finset.prod_update_of_mem hp, Finset.prod_update_of_mem hp,
      Finset.prod_update_of_mem hp]
    ring
  · rw [Finset.prod_update_of_not_mem hp, Finset.prod_update_of_not_mem hp,
      Finset.prod_update_of_not_mem hp, ← add_mul, hab, one_mul]

noncomputable def finiteSupValue {X J : Type*} [Fintype J] [Nonempty J]
    (f : J → X → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => f j x)

theorem finiteSupValue_convexOn_of_affine
    {X J : Type*} [AddCommMonoid X] [Module ℝ X] [Fintype J] [Nonempty J]
    (f : J → X → ℝ) {s : Set X} (hs : Convex ℝ s)
    (hf : ∀ j x y a b, a + b = 1 →
      f j (a • x + b • y) = a * f j x + b * f j y) :
    ConvexOn ℝ s (finiteSupValue f) := by
  constructor
  · exact hs
  · intro x hx y hy a b ha hb hab
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro j hj
    rw [hf j x y a b hab]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun j => f j x) (Finset.mem_univ j)) ha)
      (mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun j => f j y) (Finset.mem_univ j)) hb)

theorem convexOn_of_affine_combo
    {X : Type*} [AddCommMonoid X] [Module ℝ X]
    (f : X → ℝ) {s : Set X} (hs : Convex ℝ s)
    (hf : ∀ x y a b, a + b = 1 →
      f (a • x + b • y) = a * f x + b * f y) :
    ConvexOn ℝ s f := by
  constructor
  · exact hs
  · intro x hx y hy a b ha hb hab
    rw [hf x y a b hab]
    rfl

def replaceQCoordinate
    {P : Type*} [DecidableEq P]
    (q : P → RootedLeaf → ℝ) (p : P) (z : RootedLeaf → ℝ) :
    P → RootedLeaf → ℝ :=
  fun r leaf => Function.update (fun s => q s leaf) p (z leaf) r

theorem residualOutsideProduct_replace_combo
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (q : P → RootedLeaf → ℝ) (p : P)
    (z₁ z₂ : RootedLeaf → ℝ) (leaf : RootedLeaf)
    (a b : ℝ) (hab : a + b = 1) :
    residualOutsideProduct T (replaceQCoordinate q p (a • z₁ + b • z₂)) leaf =
      a * residualOutsideProduct T (replaceQCoordinate q p z₁) leaf +
        b * residualOutsideProduct T (replaceQCoordinate q p z₂) leaf := by
  unfold residualOutsideProduct replaceQCoordinate
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact finset_prod_update_combo _ _ p _ _ a b hab

noncomputable def weightedOutsideSum
    {P : Type*} [Fintype P] [DecidableEq P]
    (region : Finset RootedLeaf) (τ : RootedLeaf → ℝ) (T : Finset P)
    (q : P → RootedLeaf → ℝ) (p : P) (z : RootedLeaf → ℝ) : ℝ :=
  ∑ leaf ∈ region, τ leaf * residualOutsideProduct T (replaceQCoordinate q p z) leaf

theorem weightedOutsideSum_combo
    {P : Type*} [Fintype P] [DecidableEq P]
    (region : Finset RootedLeaf) (τ : RootedLeaf → ℝ) (T : Finset P)
    (q : P → RootedLeaf → ℝ) (p : P)
    (z₁ z₂ : RootedLeaf → ℝ) (a b : ℝ) (hab : a + b = 1) :
    weightedOutsideSum region τ T q p (a • z₁ + b • z₂) =
      a * weightedOutsideSum region τ T q p z₁ +
        b * weightedOutsideSum region τ T q p z₂ := by
  unfold weightedOutsideSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leaf hleaf
  rw [residualOutsideProduct_replace_combo T q p z₁ z₂ leaf a b hab]
  ring

theorem residualL0_qblock_convexOn
    {P : Type*} [Fintype P] [DecidableEq P]
    (τ : RootedLeaf → ℝ) (T : Finset P) (q : P → RootedLeaf → ℝ) (p : P)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun z => residualL0ForSupport T τ (replaceQCoordinate q p z)) := by
  apply convexOn_of_affine_combo _ hs
  intro x y a b hab
  simpa [residualL0ForSupport, residualL0, weightedOutsideSum] using
    (weightedOutsideSum_combo (Finset.univ : Finset RootedLeaf) τ T q p x y a b hab)

theorem skeleton_qblock_convexOn
    {P : Type*} [Fintype P] [DecidableEq P]
    (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) (p : P)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun z => SkeletonCovered τ (replaceQCoordinate q p z)) := by
  apply convexOn_of_affine_combo _ hs
  intro x y a b hab
  unfold SkeletonCovered
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leaf hleaf
  have hprod := residualOutsideProduct_replace_combo (∅ : Finset P) q p x y leaf a b hab
  simp [residualOutsideProduct] at hprod
  rw [hprod]
  have hbexpr : b = 1 - a := by linarith
  rw [hbexpr]
  ring

theorem residualL1_qblock_convexOn
    {P : Type*} [Fintype P] [DecidableEq P]
    (τ : RootedLeaf → ℝ) (T : Finset P) (q : P → RootedLeaf → ℝ) (p : P)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun z => residualL1ForSupport T τ (replaceQCoordinate q p z)) := by
  let f : RootedBranch → (RootedLeaf → ℝ) → ℝ := fun branch z =>
    weightedOutsideSum (Finset.univ.filter fun leaf => leafBranch leaf = branch)
      τ T q p z
  have hf : ∀ j x y a b, a + b = 1 →
      f j (a • x + b • y) = a * f j x + b * f j y := by
    intro j x y a b hab
    exact weightedOutsideSum_combo _ τ T q p x y a b hab
  convert finiteSupValue_convexOn_of_affine f hs hf using 1

theorem residualL2_qblock_convexOn
    {P : Type*} [Fintype P] [DecidableEq P]
    (τ : RootedLeaf → ℝ) (T : Finset P) (q : P → RootedLeaf → ℝ) (p : P)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun z => residualL2ForSupport T τ (replaceQCoordinate q p z)) := by
  let f : RootedNode → (RootedLeaf → ℝ) → ℝ := fun node z =>
    weightedOutsideSum (Finset.univ.filter fun leaf => leafNode leaf = node)
      τ T q p z
  have hf : ∀ j x y a b, a + b = 1 →
      f j (a • x + b • y) = a * f j x + b * f j y := by
    intro j x y a b hab
    exact weightedOutsideSum_combo _ τ T q p x y a b hab
  convert finiteSupValue_convexOn_of_affine f hs hf using 1

theorem residualL3_qblock_convexOn
    {P : Type*} [Fintype P] [DecidableEq P]
    (τ : RootedLeaf → ℝ) (T : Finset P) (q : P → RootedLeaf → ℝ) (p : P)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun z => residualL3ForSupport T τ (replaceQCoordinate q p z)) := by
  let f : RootedLeaf → (RootedLeaf → ℝ) → ℝ := fun leaf z =>
    τ leaf * residualOutsideProduct T (replaceQCoordinate q p z) leaf
  have hf : ∀ j x y a b, a + b = 1 →
      f j (a • x + b • y) = a * f j x + b * f j y := by
    intro j x y a b hab
    dsimp only [f]
    rw [residualOutsideProduct_replace_combo T q p x y j a b hab]
    ring
  convert finiteSupValue_convexOn_of_affine f hs hf using 1

theorem residualH_qblock_convexOn
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (q : P → RootedLeaf → ℝ) (p : P)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun z => residualHForSupport T (replaceQCoordinate q p z)) := by
  let f : RootedLeaf → (RootedLeaf → ℝ) → ℝ := fun leaf z =>
    residualOutsideProduct T (replaceQCoordinate q p z) leaf
  have hf : ∀ j x y a b, a + b = 1 →
      f j (a • x + b • y) = a * f j x + b * f j y := by
    intro j x y a b hab
    exact residualOutsideProduct_replace_combo T q p x y j a b hab
  convert finiteSupValue_convexOn_of_affine f hs hf using 1

theorem residualSupportBudget_mono
    {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset P) (β β' : P → ℝ)
    (hβ0 : ∀ p ∈ T, 0 ≤ β p) (hmono : ∀ p ∈ T, β p ≤ β' p) :
    residualSupportBudget β T ≤ residualSupportBudget β' T := by
  exact Finset.prod_le_prod hβ0 hmono

/-- Pointwise coefficient monotonicity of the complete clipped functional. -/
theorem clippedStageFunctional_mono_budget
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) (τ : RootedLeaf → ℝ)
    (x : P → RootedAxisExposure) (β β' : P → ℝ)
    (hτ : ∀ a, 0 ≤ τ a)
    (hpath : ∀ p a,
      (x p).level1 (leafBranch a) + (x p).level2 (leafNode a) +
        (if p ∈ promoted then (x p).level3 a else 0) ≤ 1)
    (hβ0 : ∀ p, 0 ≤ β p) (hmono : ∀ p, β p ≤ β' p) :
    clippedStageFunctional promoted β τ x ≤
      clippedStageFunctional promoted β' τ x := by
  let q := axisPathComplement promoted x
  have hq : ∀ p a, 0 ≤ q p a := axisPathComplement_nonneg promoted x hpath
  have hR (T : Finset P) : ∀ a, 0 ≤ residualOutsideProduct T q a :=
    residualOutsideProduct_nonneg T q hq
  have hB (T : Finset P) :
      residualSupportBudget β T ≤ residualSupportBudget β' T :=
    residualSupportBudget_mono T β β'
      (fun p hp => hβ0 p) (fun p hp => hmono p)
  have hL0 (T : Finset P) : 0 ≤ residualL0ForSupport T τ q :=
    residualL0_nonneg τ _ hτ (hR T)
  have hL1 (T : Finset P) : 0 ≤ residualL1ForSupport T τ q :=
    residualL1_nonneg τ _ hτ (hR T)
  have hL2 (T : Finset P) : 0 ≤ residualL2ForSupport T τ q :=
    residualL2_nonneg τ _ hτ (hR T)
  have hL3 (T : Finset P) : 0 ≤ residualL3ForSupport T τ q :=
    residualL3_nonneg τ _ hτ (hR T)
  have hH (T : Finset P) : 0 ≤ residualHForSupport T q :=
    residualH_nonneg _ (hR T)
  unfold clippedStageFunctional clippedFunctionalFromQ
  apply add_le_add
  · apply add_le_add
    · apply add_le_add_left
      apply Finset.sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_right (hB T)
      nlinarith [hL0 T, hL1 T, hL2 T, hL3 T]
    · apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (hB {p}) (hL3 {p})
  · apply Finset.sum_le_sum
    intro T hT
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hB T) (by norm_num)) (hH T)

end SevenPrime
