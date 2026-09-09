import Mathlib

/-!
# Concrete covering systems over `ZMod`

This module supplies the arithmetic model used by Lemma 2.1.  A displayed
class stores an integer representative, while membership is equality in the
corresponding `ZMod`.
-/

namespace SevenPrime

structure ZModClass where
  modulus : ℕ
  residue : ℤ
deriving DecidableEq

def ZModClass.Contains (c : ZModClass) (z : ℤ) : Prop :=
  (z : ZMod c.modulus) = (c.residue : ZMod c.modulus)

def ZModClass.ValidFor (N : ℕ) (c : ZModClass) : Prop :=
  1 < c.modulus ∧ c.modulus ∣ N

def ZModClassesCover (classes : Finset ZModClass) : Prop :=
  ∀ z : ℤ, ∃ c ∈ classes, c.Contains z

def ZModClassesDistinct (classes : Finset ZModClass) : Prop :=
  Set.InjOn ZModClass.modulus (classes : Set ZModClass)

def moduliLCM (classes : Finset ZModClass) : ℕ :=
  classes.lcm ZModClass.modulus

structure ConcreteCoveringSystem (N : ℕ) where
  classes : Finset ZModClass
  N_ne_zero : N ≠ 0
  valid : ∀ c ∈ classes, c.ValidFor N
  cover : ZModClassesCover classes
  distinct : ZModClassesDistinct classes
  lcm_eq : moduliLCM classes = N

def zeroClass (d : ℕ) : ZModClass := ⟨d, 0⟩

def missingDivisors (N : ℕ) (classes : Finset ZModClass) : Finset ℕ :=
  N.divisors.filter fun d => 1 < d ∧ ∀ c ∈ classes, c.modulus ≠ d

def divisorCompletionClasses (N : ℕ)
    (classes : Finset ZModClass) : Finset ZModClass :=
  classes ∪ (missingDivisors N classes).image zeroClass

theorem classes_subset_divisorCompletion (N : ℕ)
    (classes : Finset ZModClass) :
    classes ⊆ divisorCompletionClasses N classes :=
  Finset.subset_union_left

theorem zeroClass_injective : Function.Injective zeroClass := by
  intro a b h
  exact congrArg ZModClass.modulus h

theorem divisorCompletion_valid {N : ℕ} {classes : Finset ZModClass}
    (hvalid : ∀ c ∈ classes, c.ValidFor N) :
    ∀ c ∈ divisorCompletionClasses N classes, c.ValidFor N := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact hvalid c hc
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    have hd' := (Finset.mem_filter.mp hd)
    exact ⟨hd'.2.1, (Nat.mem_divisors.mp hd'.1).1⟩

theorem divisorCompletion_covers {N : ℕ} {classes : Finset ZModClass}
    (hcover : ZModClassesCover classes) :
    ZModClassesCover (divisorCompletionClasses N classes) := by
  intro z
  obtain ⟨c, hc, hz⟩ := hcover z
  exact ⟨c, classes_subset_divisorCompletion N classes hc, hz⟩

theorem divisorCompletion_distinct {N : ℕ} {classes : Finset ZModClass}
    (hdistinct : ZModClassesDistinct classes) :
    ZModClassesDistinct (divisorCompletionClasses N classes) := by
  intro c hc d hd hmod
  rcases Finset.mem_union.mp hc with hc | hc <;>
    rcases Finset.mem_union.mp hd with hd | hd
  · exact hdistinct hc hd hmod
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
    have hmissing := (Finset.mem_filter.mp hk).2.2
    exact False.elim (hmissing c hc hmod)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    have hmissing := (Finset.mem_filter.mp hk).2.2
    exact False.elim (hmissing d hd hmod.symm)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, hl, hzero⟩ := Finset.mem_image.mp hd
    subst d
    have hkl : k = l := by
      simpa [zeroClass] using hmod
    exact congrArg zeroClass hkl

theorem divisorCompletion_has_every_divisor
    {N : ℕ} (hN : N ≠ 0) (classes : Finset ZModClass)
    {d : ℕ} (hd : d ∣ N) (hd1 : 1 < d) :
    ∃ c ∈ divisorCompletionClasses N classes, c.modulus = d := by
  by_cases hused : ∃ c ∈ classes, c.modulus = d
  · obtain ⟨c, hc, hcd⟩ := hused
    exact ⟨c, classes_subset_divisorCompletion N classes hc, hcd⟩
  · have hddiv : d ∈ N.divisors := Nat.mem_divisors.mpr ⟨hd, hN⟩
    have hdmissing : d ∈ missingDivisors N classes := by
      apply Finset.mem_filter.mpr
      exact ⟨hddiv, hd1, fun c hc hcd => hused ⟨c, hc, hcd⟩⟩
    refine ⟨zeroClass d, ?_, rfl⟩
    exact Finset.mem_union_right classes (Finset.mem_image.mpr ⟨d, hdmissing, rfl⟩)

theorem divisorCompletion_lcm {N : ℕ} {classes : Finset ZModClass}
    (hlcm : moduliLCM classes = N)
    (hvalid : ∀ c ∈ divisorCompletionClasses N classes, c.ValidFor N) :
    moduliLCM (divisorCompletionClasses N classes) = N := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro c hc
    exact (hvalid c hc).2
  · have hmono : moduliLCM classes ∣
        moduliLCM (divisorCompletionClasses N classes) :=
      Finset.lcm_mono (classes_subset_divisorCompletion N classes)
    exact hlcm ▸ hmono

def ConcreteCoveringSystem.divisorCompletion {N : ℕ}
    (S : ConcreteCoveringSystem N) : ConcreteCoveringSystem N where
  classes := divisorCompletionClasses N S.classes
  N_ne_zero := S.N_ne_zero
  valid := divisorCompletion_valid S.valid
  cover := divisorCompletion_covers S.cover
  distinct := divisorCompletion_distinct S.distinct
  lcm_eq := divisorCompletion_lcm S.lcm_eq (divisorCompletion_valid S.valid)

/-- Concrete form of Lemma 2.1: completion preserves covering and distinctness,
keeps the same LCM, and provides a class for every nontrivial divisor. -/
theorem lemma_2_1_concrete_divisor_completion {N : ℕ}
    (S : ConcreteCoveringSystem N) :
    ZModClassesCover S.divisorCompletion.classes ∧
      ZModClassesDistinct S.divisorCompletion.classes ∧
      moduliLCM S.divisorCompletion.classes = N ∧
      ∀ d, d ∣ N → 1 < d →
        ∃ c ∈ S.divisorCompletion.classes, c.modulus = d := by
  exact ⟨S.divisorCompletion.cover, S.divisorCompletion.distinct,
    S.divisorCompletion.lcm_eq,
    fun d hd hd1 => divisorCompletion_has_every_divisor S.N_ne_zero S.classes hd hd1⟩

/-! ## Concrete pure-prime-power slices -/

open scoped BigOperators

private theorem addHom_fiber_card_mul {A B : Type*}
    [AddGroup A] [AddGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (f : A →+ B) (hf : Function.Surjective f) (y : B) :
    Fintype.card {x : A // f x = y} * Fintype.card B = Fintype.card A := by
  have heq (z : B) :
      Fintype.card {x : A // f x = z} = Fintype.card {x : A // f x = y} := by
    exact Fintype.card_congr (f.fiberEquivOfSurjective hf z y)
  have hsigma := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at hsigma
  simp_rw [heq] at hsigma
  simpa [mul_comm] using hsigma

/-- A level-`f` residue class, pulled back to the top coordinate `ZMod (p^e)`. -/
def primePowerSlice (p e f : ℕ) (hf : f ≤ e)
    (a : ZMod (p ^ f)) : Set (ZMod (p ^ e)) :=
  {x | ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ f)) x = a}

theorem primePowerCast_surjective (p e f : ℕ) (hf : f ≤ e) :
    Function.Surjective
      (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ f))) := by
  intro y
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  exact ⟨(k : ZMod (p ^ e)), by simp⟩

/-- A level-`f` slice in `ZMod (p^e)` has exactly `p^(e-f)` elements. -/
theorem primePowerSlice_ncard (p e f : ℕ) (hp : 0 < p) (hf : f ≤ e)
    (a : ZMod (p ^ f)) :
    (primePowerSlice p e f hf a).ncard = p ^ (e - f) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e (Nat.ne_of_gt hp)⟩
  letI : NeZero (p ^ f) := ⟨pow_ne_zero f (Nat.ne_of_gt hp)⟩
  let φ := (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ f))).toAddMonoidHom
  have hmul := addHom_fiber_card_mul φ (primePowerCast_surjective p e f hf) a
  rw [ZMod.card, ZMod.card] at hmul
  rw [← Nat.card_eq_fintype_card] at hmul
  have hncard : Nat.card {x : ZMod (p ^ e) // φ x = a} =
      (primePowerSlice p e f hf a).ncard := by
    change Nat.card (↥({x | φ x = a} : Set (ZMod (p ^ e)))) = _
    rw [Set.Nat.card_coe_set_eq]
    rfl
  rw [hncard] at hmul
  change (primePowerSlice p e f hf a).ncard * p ^ f = p ^ e at hmul
  apply Nat.mul_right_cancel (pow_pos hp f)
  calc
    (primePowerSlice p e f hf a).ncard * p ^ f = p ^ e := hmul
    _ = p ^ (e - f) * p ^ f := by
      rw [← pow_add, Nat.sub_add_cancel hf]

theorem ncard_finset_sup_le {I A : Type*} [Finite A]
    (s : Finset I) (U : I → Set A) :
    (s.sup U).ncard ≤ ∑ i ∈ s, (U i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sum_insert ha]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- The union removed by choosing one residue class at every level `1,...,e`. -/
def pureTowerRemoved (p e : ℕ)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1))) : Set (ZMod (p ^ e)) :=
  Finset.univ.sup fun i =>
    primePowerSlice p e (i.val + 1) (Nat.succ_le_iff.mpr i.isLt) (r i)

theorem pureTowerRemoved_ncard_le (p e : ℕ) (hp : 0 < p)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1))) :
    (pureTowerRemoved p e r).ncard ≤
      ∑ i : Fin e, p ^ (e - (i.val + 1)) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e (Nat.ne_of_gt hp)⟩
  have h := ncard_finset_sup_le (Finset.univ : Finset (Fin e))
    (fun i => primePowerSlice p e (i.val + 1)
      (Nat.succ_le_iff.mpr i.isLt) (r i))
  calc
    (pureTowerRemoved p e r).ncard ≤
        ∑ i : Fin e,
          (primePowerSlice p e (i.val + 1)
            (Nat.succ_le_iff.mpr i.isLt) (r i)).ncard := h
    _ = ∑ i : Fin e, p ^ (e - (i.val + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [primePowerSlice_ncard p e (i.val + 1) hp
        (Nat.succ_le_iff.mpr i.isLt) (r i)]

/-- The points in the top coordinate that avoid all selected tower classes. -/
def concretePureTowerSurvivor (p e : ℕ)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1))) : Set (ZMod (p ^ e)) :=
  (pureTowerRemoved p e r)ᶜ

theorem concretePureTowerSurvivor_ncard (p e : ℕ) (hp : 0 < p)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1))) :
    (concretePureTowerSurvivor p e r).ncard =
      p ^ e - (pureTowerRemoved p e r).ncard := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e (Nat.ne_of_gt hp)⟩
  have h := Set.ncard_diff (s := pureTowerRemoved p e r) (t := Set.univ)
    (Set.subset_univ _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card] at h
  rw [concretePureTowerSurvivor, Set.compl_eq_univ_diff]
  exact h

/-- Concrete cardinality form of Lemma 3.1.  The right-hand sum is the total
capacity of one selected congruence class at each pure prime-power level. -/
theorem lemma_3_1_concrete_pure_tower_survivor (p e : ℕ) (hp : 0 < p)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1))) :
    p ^ e - ∑ i : Fin e, p ^ (e - (i.val + 1)) ≤
      (concretePureTowerSurvivor p e r).ncard := by
  rw [concretePureTowerSurvivor_ncard p e hp r]
  exact Nat.sub_le_sub_left (pureTowerRemoved_ncard_le p e hp r) (p ^ e)

theorem reverse_prime_power_sum (p e : ℕ) :
    (∑ i : Fin e, p ^ (e - (i.val + 1))) =
      ∑ i ∈ Finset.range e, p ^ i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa [Function.comp_def, Fin.rev] using
    (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin e))
      (fun i : Fin e => p ^ i.val))

theorem threeTowerSurvivor_closedForm (e : ℕ) :
    3 ^ e - ∑ i : Fin e, 3 ^ (e - (i.val + 1)) = (3 ^ e + 1) / 2 := by
  rw [reverse_prime_power_sum]
  rw [Nat.geomSum_eq (by norm_num : 2 ≤ 3)]
  have hodd3 : Odd 3 := ⟨1, by norm_num⟩
  obtain ⟨k, hk⟩ : Odd (3 ^ e) := hodd3.pow
  omega

theorem concreteThreeTowerSurvivor_ncard_lower (e : ℕ)
    (r : ∀ i : Fin e, ZMod (3 ^ (i.val + 1))) :
    (3 ^ e + 1) / 2 ≤ (concretePureTowerSurvivor 3 e r).ncard := by
  rw [← threeTowerSurvivor_closedForm e]
  exact lemma_3_1_concrete_pure_tower_survivor 3 e (by norm_num) r

/-! ## Concrete finite Chinese remainder coordinates -/

open scoped Function

noncomputable def finiteCRTEquiv
    {ι : Type*} [Fintype ι] (factor : ι → ℕ)
    (hcoprime : Pairwise (Nat.Coprime on factor)) :
    ZMod (∏ i, factor i) ≃+* ∀ i, ZMod (factor i) :=
  ZMod.prodEquivPi factor hcoprime

def CRTProductSet {ι : Type*} [Fintype ι] {factor : ι → ℕ}
    (S : ∀ i, Set (ZMod (factor i))) : Set (∀ i, ZMod (factor i)) :=
  Set.univ.pi S

noncomputable def CRTProductSurvivor
    {ι : Type*} [Fintype ι] (factor : ι → ℕ)
    (hcoprime : Pairwise (Nat.Coprime on factor))
    (S : ∀ i, Set (ZMod (factor i))) : Set (ZMod (∏ i, factor i)) :=
  (finiteCRTEquiv factor hcoprime) ⁻¹' CRTProductSet S

theorem mem_CRTProductSurvivor_iff
    {ι : Type*} [Fintype ι] (factor : ι → ℕ)
    (hcoprime : Pairwise (Nat.Coprime on factor))
    (S : ∀ i, Set (ZMod (factor i))) (x : ZMod (∏ i, factor i)) :
    x ∈ CRTProductSurvivor factor hcoprime S ↔
      ∀ i, finiteCRTEquiv factor hcoprime x i ∈ S i := by
  simp [CRTProductSurvivor, CRTProductSet]

/-- Concrete CRT form of Lemma 3.2: avoiding every coordinatewise pure-tower
complement is exactly membership in the Cartesian survivor. -/
theorem lemma_3_2_concrete_crt_survivor
    {ι : Type*} [Fintype ι] (factor : ι → ℕ)
    (hcoprime : Pairwise (Nat.Coprime on factor))
    (S : ∀ i, Set (ZMod (factor i))) (x : ZMod (∏ i, factor i)) :
    (¬ ∃ i, finiteCRTEquiv factor hcoprime x i ∉ S i) ↔
      x ∈ CRTProductSurvivor factor hcoprime S := by
  rw [mem_CRTProductSurvivor_iff]
  simp

end SevenPrime
