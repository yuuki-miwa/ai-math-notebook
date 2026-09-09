import Mathlib
import SevenPrime.ConcreteCovering
import SevenPrime.AxisResidual
import SevenPrime.RootedSymmetry

/-!
# Lean formalization of Lemmas 2.1--8.1

This file isolates the mathematical kernels used in the manuscript.  The finite
certificate of Section 9 is deliberately outside the scope of this file.
-/

namespace SevenPrime

/-! ## Lemma 2.1: divisor completion -/

structure ResidueClass (α : Type*) where
  modulus : ℕ
  carrier : Set α

variable {α : Type*}

def Covers (C : Finset (ResidueClass α)) : Prop :=
  ∀ x, ∃ c ∈ C, x ∈ c.carrier

def DistinctModuli (C : Finset (ResidueClass α)) : Prop :=
  Set.InjOn ResidueClass.modulus (C : Set (ResidueClass α))

theorem lemma_2_1_divisor_completion
    [DecidableEq (ResidueClass α)]
    {old added : Finset (ResidueClass α)}
    (hcover : Covers old)
    (hold : DistinctModuli old) (hadded : DistinctModuli added)
    (hcross : ∀ c ∈ old, ∀ d ∈ added, c.modulus ≠ d.modulus) :
    Covers (old ∪ added) ∧ DistinctModuli (old ∪ added) := by
  constructor
  · intro x
    obtain ⟨c, hc, hxc⟩ := hcover x
    exact ⟨c, Finset.mem_union_left added hc, hxc⟩
  · intro c hc d hd heq
    simp only [Finset.mem_coe, Finset.mem_union] at hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exact hold hc hd heq
    · exact False.elim (hcross c hc d hd heq)
    · exact False.elim (hcross d hd c hc heq.symm)
    · exact hadded hc hd heq

/-! ## Lemmas 3.1 and 3.2: pure prime-power towers -/

open scoped BigOperators

def towerCapacity (p : ℝ) (e : ℕ) : ℝ :=
  ∑ i ∈ Finset.range e, p ^ i

noncomputable def towerSurvivorLower (p : ℝ) (e : ℕ) : ℝ :=
  ((p - 2) * p ^ e + 1) / (p - 1)

noncomputable def towerBudget (p : ℝ) (e : ℕ) : ℝ :=
  (p ^ e - 1) / ((p - 2) * p ^ e + 1)

theorem tower_survivor_closed_form {p : ℝ} (e : ℕ) (hp : p ≠ 1) :
    p ^ e - towerCapacity p e = towerSurvivorLower p e := by
  rw [towerSurvivorLower]
  apply (eq_div_iff (sub_ne_zero.mpr hp)).2
  have hgeom := geom_sum_mul p e
  dsimp [towerCapacity]
  nlinarith

theorem lemma_3_1_pure_tower_survivor_size
    {p : ℝ} {e : ℕ} {survivorMass : ℝ}
    (hp : 2 < p)
    (hunion : p ^ e - towerCapacity p e ≤ survivorMass) :
    towerSurvivorLower p e ≤ survivorMass ∧
      towerBudget p e < 1 / (p - 2) := by
  constructor
  · rwa [← tower_survivor_closed_form e (by linarith)]
  · have hpow : 0 < p ^ e := pow_pos (by linarith) e
    have hp2 : 0 < p - 2 := by linarith
    have hden : 0 < (p - 2) * p ^ e + 1 := by
      nlinarith [mul_pos hp2 hpow]
    rw [towerBudget, div_lt_div_iff₀ hden (by linarith)]
    nlinarith

variable {ι : Type*} {β : ι → Type*}

def ProductSurvivor (S : ∀ i, Set (β i)) (x : ∀ i, β i) : Prop :=
  ∀ i, x i ∈ S i

def RemovedBySomePureTower (S : ∀ i, Set (β i)) (x : ∀ i, β i) : Prop :=
  ∃ i, x i ∉ S i

theorem lemma_3_2_exact_product_survivor
    (S : ∀ i, Set (β i)) (x : ∀ i, β i) :
    ¬ RemovedBySomePureTower S x ↔ ProductSurvivor S x := by
  simp [RemovedBySomePureTower, ProductSurvivor]

/-! ## Lemmas 4.1 and 4.2: the 3-adic profile -/

def ProfilePolytope (τ : Fin 18 → ℝ) : Prop :=
  (∀ a, 0 ≤ τ a ∧ τ a ≤ 2 / 27) ∧ ∑ a, τ a = 1

theorem normalized_leaf_bound {leaf total scale : ℝ}
    (hleaf : leaf ≤ scale)
    (htotal : 27 * scale / 2 ≤ total) (htotal0 : 0 < total) :
    leaf / total ≤ 2 / 27 := by
  rw [div_le_iff₀ htotal0]
  nlinarith

/-- Pad the 3-adic exponent just enough that residue classes modulo `27 = 3^3`
exist as top-coordinate slices. -/
def paddedExponent (e : ℕ) : ℕ := max e 3

theorem exponent_le_paddedExponent (e : ℕ) : e ≤ paddedExponent e :=
  Nat.le_max_left _ _

theorem three_le_paddedExponent (e : ℕ) : 3 ≤ paddedExponent e :=
  Nat.le_max_right _ _

@[simp] theorem paddedExponent_eq_self {e : ℕ} (h3 : 3 ≤ e) :
    paddedExponent e = e :=
  Nat.max_eq_left h3

/-- Padding preserves the old 3-power as a divisor of the new top modulus. -/
theorem threePow_dvd_paddedThreePow (e : ℕ) :
    3 ^ e ∣ 3 ^ paddedExponent e :=
  pow_dvd_pow 3 (exponent_le_paddedExponent e)

/-- Normalized mass of one residue modulo `27` inside a finite 3-adic
survivor at exponent `e ≥ 3`. -/
noncomputable def concreteLeafMass (e : ℕ) (h3 : 3 ≤ e)
    (S : Set (ZMod (3 ^ e))) (a : ZMod 27) : ℝ :=
  ((S ∩ primePowerSlice 3 e 3 h3 a).ncard : ℝ) / (S.ncard : ℝ)

theorem concreteLeafMass_le_two_div_twentySeven
    (e : ℕ) (h3 : 3 ≤ e) (S : Set (ZMod (3 ^ e)))
    (hS : (3 ^ e + 1) / 2 ≤ S.ncard) (a : ZMod 27) :
    concreteLeafMass e h3 S a ≤ 2 / 27 := by
  have hleafNat :
      (S ∩ primePowerSlice 3 e 3 h3 a).ncard ≤ 3 ^ (e - 3) := by
    calc
      (S ∩ primePowerSlice 3 e 3 h3 a).ncard ≤
          (primePowerSlice 3 e 3 h3 a).ncard :=
        Set.ncard_inter_le_ncard_right _ _
      _ = 3 ^ (e - 3) :=
        primePowerSlice_ncard 3 e 3 (by norm_num) h3 a
  have hpow : 3 ^ e = 27 * 3 ^ (e - 3) := by
    calc
      3 ^ e = 3 ^ ((e - 3) + 3) := by rw [Nat.sub_add_cancel h3]
      _ = 27 * 3 ^ (e - 3) := by rw [pow_add]; norm_num; omega
  have hodd3 : Odd 3 := ⟨1, by norm_num⟩
  obtain ⟨k, hk⟩ : Odd (3 ^ e) := hodd3.pow
  have hceil : 3 ^ e ≤ 2 * ((3 ^ e + 1) / 2) := by omega
  have htotalNat : 27 * 3 ^ (e - 3) ≤ 2 * S.ncard := by
    rw [← hpow]
    exact hceil.trans (Nat.mul_le_mul_left 2 hS)
  have hleafReal :
      ((S ∩ primePowerSlice 3 e 3 h3 a).ncard : ℝ) ≤
        (3 ^ (e - 3) : ℕ) := by
    exact_mod_cast hleafNat
  have htotalReal :
      27 * ((3 ^ (e - 3) : ℕ) : ℝ) / 2 ≤ (S.ncard : ℝ) := by
    have hc : ((27 * 3 ^ (e - 3) : ℕ) : ℝ) ≤
        ((2 * S.ncard : ℕ) : ℝ) := by exact_mod_cast htotalNat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hc
    nlinarith
  have hscale : 0 < 3 ^ (e - 3) := pow_pos (by norm_num) _
  have hScard : 0 < S.ncard := by omega
  have htotal0 : (0 : ℝ) < S.ncard := by exact_mod_cast hScard
  exact normalized_leaf_bound hleafReal htotalReal htotal0

/-- Concrete padded form of Lemma 4.1: after replacing `e` by `max e 3`,
every modulo-27 leaf of the pure 3-power survivor has normalized mass at most
`2/27`. -/
theorem lemma_4_1_concrete_padded_leaf_bound (e : ℕ)
    (r : ∀ i : Fin (paddedExponent e), ZMod (3 ^ (i.val + 1)))
    (a : ZMod 27) :
    concreteLeafMass (paddedExponent e) (three_le_paddedExponent e)
      (concretePureTowerSurvivor 3 (paddedExponent e) r) a ≤ 2 / 27 := by
  apply concreteLeafMass_le_two_div_twentySeven
  exact concreteThreeTowerSurvivor_ncard_lower (paddedExponent e) r

theorem lemma_4_1_profile_polytope (τ : Fin 18 → ℝ)
    (hnonneg : ∀ a, 0 ≤ τ a)
    (hleaf : ∀ a, τ a ≤ 2 / 27)
    (hsum : ∑ a, τ a = 1) : ProfilePolytope τ := by
  exact ⟨fun a => ⟨hnonneg a, hleaf a⟩, hsum⟩

def BoxSlice {n : ℕ} (u total : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ k, 0 ≤ x k ∧ x k ≤ u) ∧ ∑ k, x k = total}

def balancedPerturb {n : ℕ} (x : Fin n → ℝ)
    (i j : Fin n) (ε : ℝ) : Fin n → ℝ :=
  Function.update (Function.update x i (x i + ε)) j (x j - ε)

theorem balancedPerturb_sum {n : ℕ} (x : Fin n → ℝ)
    {i j : Fin n} (hij : i ≠ j) (ε : ℝ) :
    ∑ k, balancedPerturb x i j ε k = ∑ k, x k := by
  classical
  simp [balancedPerturb, Finset.sum_update_of_mem, hij, hij.symm]
  ring

theorem balancedPerturb_mem_boxSlice {n : ℕ} {u total : ℝ}
    {x : Fin n → ℝ} (hx : x ∈ BoxSlice u total)
    {i j : Fin n} (hij : i ≠ j) {ε : ℝ}
    (hε0 : 0 ≤ ε)
    (hεi0 : ε ≤ x i) (hεiu : ε ≤ u - x i)
    (hεj0 : ε ≤ x j) (hεju : ε ≤ u - x j) :
    balancedPerturb x i j ε ∈ BoxSlice u total ∧
      balancedPerturb x i j (-ε) ∈ BoxSlice u total := by
  classical
  have hcoord (k : Fin n) :
      (0 ≤ balancedPerturb x i j ε k ∧ balancedPerturb x i j ε k ≤ u) ∧
      (0 ≤ balancedPerturb x i j (-ε) k ∧ balancedPerturb x i j (-ε) k ≤ u) := by
    by_cases hki : k = i
    · subst k
      simp [balancedPerturb, hij]
      constructor <;> constructor <;> nlinarith [hx.1 i]
    · by_cases hkj : k = j
      · subst k
        simp [balancedPerturb, hij, hij.symm]
        constructor <;> constructor <;> nlinarith [hx.1 j]
      · simp [balancedPerturb, hki, hkj, hx.1 k]
  constructor
  · exact ⟨fun k => (hcoord k).1,
      (balancedPerturb_sum x hij ε).trans hx.2⟩
  · exact ⟨fun k => (hcoord k).2,
      (balancedPerturb_sum x hij (-ε)).trans hx.2⟩

theorem balancedPerturb_midpoint {n : ℕ} (x : Fin n → ℝ)
    {i j : Fin n} (hij : i ≠ j) (ε : ℝ) :
    (2 : ℝ)⁻¹ • balancedPerturb x i j ε +
      (2 : ℝ)⁻¹ • balancedPerturb x i j (-ε) = x := by
  classical
  funext k
  by_cases hki : k = i
  · subst k
    simp [balancedPerturb, hij]
    ring
  · by_cases hkj : k = j
    · subst k
      simp [balancedPerturb, hij, hij.symm]
      ring
    · simp [balancedPerturb, hki, hkj]
      ring

/-- Two independently movable interior coordinates contradict extremality. -/
theorem not_extremePoint_of_balanced_perturbation {n : ℕ} {u total : ℝ}
    {x : Fin n → ℝ} {i j : Fin n} (hij : i ≠ j) {ε : ℝ}
    (hε : 0 < ε)
    (hmemPlus : balancedPerturb x i j ε ∈ BoxSlice u total)
    (hmemMinus : balancedPerturb x i j (-ε) ∈ BoxSlice u total) :
    x ∉ (BoxSlice u total).extremePoints ℝ := by
  intro hxext
  have hxseg : x ∈ openSegment ℝ (balancedPerturb x i j ε)
      (balancedPerturb x i j (-ε)) := by
    refine ⟨(2 : ℝ)⁻¹, (2 : ℝ)⁻¹, by norm_num, by norm_num, by norm_num, ?_⟩
    exact balancedPerturb_midpoint x hij ε
  have heq := (mem_extremePoints_iff_left.mp hxext).2
    _ hmemPlus _ hmemMinus hxseg
  have hi := congrFun heq i
  simp [balancedPerturb, hij] at hi
  linarith

/-- An extreme point of a box cut by one sum hyperplane has at most one
coordinate strictly between the two box endpoints. -/
theorem lemma_4_2_vertex_endpoint_property {n : ℕ} {u total : ℝ}
    {x : Fin n → ℝ} (hxext : x ∈ (BoxSlice u total).extremePoints ℝ) :
    ∀ i j, 0 < x i → x i < u → 0 < x j → x j < u → i = j := by
  intro i j hi0 hiu hj0 hju
  by_contra hij
  let δ := min (min (x i) (u - x i)) (min (x j) (u - x j))
  let ε := δ / 2
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact lt_min (lt_min hi0 (sub_pos.mpr hiu))
      (lt_min hj0 (sub_pos.mpr hju))
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεi0 : ε ≤ x i := by
    have hδ := min_le_left (min (x i) (u - x i)) (min (x j) (u - x j))
    have hii := min_le_left (x i) (u - x i)
    dsimp [ε]
    nlinarith
  have hεiu : ε ≤ u - x i := by
    have hδ := min_le_left (min (x i) (u - x i)) (min (x j) (u - x j))
    have hii := min_le_right (x i) (u - x i)
    dsimp [ε]
    nlinarith
  have hεj0 : ε ≤ x j := by
    have hδ := min_le_right (min (x i) (u - x i)) (min (x j) (u - x j))
    have hjj := min_le_left (x j) (u - x j)
    dsimp [ε]
    nlinarith
  have hεju : ε ≤ u - x j := by
    have hδ := min_le_right (min (x i) (u - x i)) (min (x j) (u - x j))
    have hjj := min_le_right (x j) (u - x j)
    dsimp [ε]
    nlinarith
  have hmem := balancedPerturb_mem_boxSlice hxext.1 hij hε0.le
    hεi0 hεiu hεj0 hεju
  exact (not_extremePoint_of_balanced_perturbation hij hε0 hmem.1 hmem.2) hxext

theorem lemma_4_2_exists_exceptional_coordinate
    {w : Fin 18 → ℝ} (hw : w ∈ BoxSlice 2 27)
    (hatMostOne : ∀ i j, 0 < w i → w i < 2 → 0 < w j → w j < 2 → i = j) :
    ∃ e, ∀ i, i ≠ e → w i = 0 ∨ w i = 2 := by
  have endpoint_of_not_interior (i : Fin 18)
      (hi : ¬ (0 < w i ∧ w i < 2)) : w i = 0 ∨ w i = 2 := by
    by_cases hi0 : w i = 0
    · exact Or.inl hi0
    · right
      have hpos : 0 < w i := lt_of_le_of_ne (hw.1 i).1 (Ne.symm hi0)
      exact le_antisymm (hw.1 i).2 (le_of_not_gt fun hlt => hi ⟨hpos, hlt⟩)
  by_cases h : ∃ e, 0 < w e ∧ w e < 2
  · obtain ⟨e, he0, heu⟩ := h
    refine ⟨e, fun i hie => endpoint_of_not_interior i ?_⟩
    rintro ⟨hi0, hiu⟩
    exact hie (hatMostOne i e hi0 hiu he0 heu)
  · refine ⟨0, fun i _ => endpoint_of_not_interior i ?_⟩
    exact fun hi => h ⟨i, hi⟩

/-- The endpoint property plus the sum `27` gives the complete multiset
`0^4, 1^1, 2^13`, without assuming integrality of the exceptional value. -/
theorem lemma_4_2_concrete_multiplicities
    {w : Fin 18 → ℝ} (hw : w ∈ BoxSlice 2 27)
    {e : Fin 18} (hendpoint : ∀ i, i ≠ e → w i = 0 ∨ w i = 2) :
    w e = 1 ∧
      (Finset.univ.filter fun i => w i = 0).card = 4 ∧
      (Finset.univ.filter fun i => w i = 2).card = 13 := by
  classical
  let s : Finset (Fin 18) := Finset.univ.erase e
  let T := s.filter fun i => w i = 2
  let Z := s.filter fun i => w i = 0
  have hsumErase : ∑ i ∈ s, w i = 2 * T.card := by
    calc
      ∑ i ∈ s, w i = ∑ i ∈ s, if w i = 2 then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hie : i ≠ e := by simpa [s] using hi
        rcases hendpoint i hie with hi0 | hi2
        · simp [hi0]
        · simp [hi2]
      _ = ∑ i ∈ s, (if w i = 2 then (1 : ℝ) else 0) * 2 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
      _ = 2 * T.card := by
        rw [← Finset.sum_mul, Finset.sum_boole]
        simp [T]
        ring
  have hdecomp := Finset.add_sum_erase Finset.univ w (Finset.mem_univ e)
  have heq : w e + 2 * T.card = 27 := by
    rw [hsumErase] at hdecomp
    exact hdecomp.trans hw.2
  have hTlt : T.card < 14 := by
    exact_mod_cast (show (T.card : ℝ) < 14 by nlinarith [hw.1 e])
  have hTgt : 12 < T.card := by
    exact_mod_cast (show (12 : ℝ) < T.card by nlinarith [hw.1 e])
  have hTcard : T.card = 13 := by omega
  have hwe : w e = 1 := by rw [hTcard] at heq; norm_num at heq ⊢; linarith
  have hZeq : Z = s.filter (fun i => ¬ w i = 2) := by
    ext i
    simp only [Z, Finset.mem_filter]
    constructor
    · rintro ⟨his, hi0⟩
      exact ⟨his, by simp [hi0]⟩
    · rintro ⟨his, hi2⟩
      have hie : i ≠ e := by simpa [s] using his
      rcases hendpoint i hie with hi0 | hi2'
      · exact ⟨his, hi0⟩
      · exact False.elim (hi2 hi2')
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := s) (fun i => w i = 2)
  have hscard : s.card = 17 := by simp [s]
  have hZcard : Z.card = 4 := by
    change T.card + (s.filter fun i => ¬ w i = 2).card = s.card at hpartition
    rw [← hZeq] at hpartition
    omega
  have hzeroGlobal :
      (Finset.univ.filter fun i => w i = 0) = Z := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Z, s,
      Finset.mem_erase]
    constructor
    · intro hi
      have hie : i ≠ e := by
        intro h
        subst i
        linarith
      exact ⟨⟨hie, trivial⟩, hi⟩
    · exact fun hi => hi.2
  have htwoGlobal :
      (Finset.univ.filter fun i => w i = 2) = T := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, s,
      Finset.mem_erase]
    constructor
    · intro hi
      have hie : i ≠ e := by
        intro h
        subst i
        linarith
      exact ⟨⟨hie, trivial⟩, hi⟩
    · exact fun hi => hi.2
  exact ⟨hwe, by simpa [hzeroGlobal] using hZcard,
    by simpa [htwoGlobal] using hTcard⟩

theorem lemma_4_2_vertices_of_K3 {w : Fin 18 → ℝ}
    (hwext : w ∈ (BoxSlice 2 27).extremePoints ℝ) :
    ∃ e, w e = 1 ∧
      (Finset.univ.filter fun i => w i = 0).card = 4 ∧
      (Finset.univ.filter fun i => w i = 2).card = 13 := by
  have hatMostOne := lemma_4_2_vertex_endpoint_property hwext
  obtain ⟨e, he⟩ := lemma_4_2_exists_exceptional_coordinate hwext.1 hatMostOne
  exact ⟨e, lemma_4_2_concrete_multiplicities hwext.1 he⟩

/-- The arithmetic forced after the box/hyperplane vertex argument: seventeen
endpoint coordinates and at most one exceptional coordinate. -/
theorem lemma_4_2_vertex_multiplicities
    {zeros twos exceptional : ℕ}
    (hendpoints : zeros + twos = 17)
    (hexceptional : exceptional ≤ 1)
    (hsum : exceptional + 2 * twos = 27) :
    zeros = 4 ∧ exceptional = 1 ∧ twos = 13 := by omega

theorem lemma_4_2_labelled_vertex_count :
    18 * Nat.choose 17 4 = 42840 := by norm_num [Nat.choose]

/-! ## Lemmas 5.1 and 5.2: axis skeletons -/

theorem lemma_5_1_levelwise_axis_budget
    {V F : Type*} [Fintype V] [Fintype F]
    (x : V → ℝ) (capacity : F → ℝ) (b β : ℝ)
    (hx : ∀ v, 0 ≤ x v)
    (hdisjointize : ∑ v, x v ≤ ∑ f, capacity f)
    (hcapacity : ∑ f, capacity f ≤ b) (hb : b < β) :
    (∀ v, 0 ≤ x v) ∧ ∑ v, x v ≤ b ∧ ∑ v, x v < β := by
  exact ⟨hx, hdisjointize.trans hcapacity,
    lt_of_le_of_lt (hdisjointize.trans hcapacity) hb⟩

theorem concretePureTowerSurvivor_ncard_pos_of_two_lt
    (p e : ℕ) (hp : 2 < p)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1))) :
    0 < (concretePureTowerSurvivor p e r).ncard := by
  have hsurv := lemma_3_1_concrete_pure_tower_survivor p e (by omega) r
  rw [reverse_prime_power_sum] at hsurv
  have hsumlt : (∑ i ∈ Finset.range e, p ^ i) < p ^ e :=
    Nat.geomSum_lt (by omega) (fun k hk => Finset.mem_range.mp hk)
  omega

theorem concreteAxisBudget_lt_beta
    (p e : ℕ) (hp : 2 < p)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1))) :
    concreteAxisBudget p e (concretePureTowerSurvivor p e r) <
      1 / ((p : ℝ) - 2) := by
  let A := ∑ i : Fin e, p ^ (e - (i.val + 1))
  let S := concretePureTowerSurvivor p e r
  have hsurv : p ^ e - A ≤ S.ncard := by
    exact lemma_3_1_concrete_pure_tower_survivor p e (by omega) r
  have hgeom : A * (p - 1) + 1 = p ^ e := by
    rw [show A = ∑ i ∈ Finset.range e, p ^ i by
      exact reverse_prime_power_sum p e]
    have h := geom_sum_mul_add (p - 1) e
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using h
  have hdecomp : (p - 2) * A + A + 1 = p ^ e := by
    calc
      (p - 2) * A + A + 1 = A * ((p - 2) + 1) + 1 := by ring
      _ = A * (p - 1) + 1 := by rw [show p - 2 + 1 = p - 1 by omega]
      _ = p ^ e := hgeom
  have hcrossNat : (p - 2) * A < S.ncard := by
    apply lt_of_lt_of_le _ hsurv
    omega
  have hSposNat : 0 < S.ncard := by omega
  have hSpos : (0 : ℝ) < S.ncard := by exact_mod_cast hSposNat
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
    norm_num only [Nat.cast_ofNat, sub_pos]
    exact_mod_cast hp
  unfold concreteAxisBudget
  rw [← Nat.cast_sum]
  change (A : ℝ) / (S.ncard : ℝ) < 1 / ((p : ℝ) - 2)
  rw [div_lt_div_iff₀ hSpos hp2]
  norm_num only [one_mul]
  have hc : (((p - 2 : ℕ) : ℝ) * (A : ℝ)) < (S.ncard : ℝ) := by
    exact_mod_cast hcrossNat
  rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat] at hc
  nlinarith

/-- Fully concrete Lemma 5.1 for one fixed prime and 3-adic level.  The
middle quantity is the finite tower budget `b_p(e)` computed from actual
cardinalities, and the final strict bound is `β_p = 1/(p-2)`. -/
theorem lemma_5_1_concrete_axis_budget_beta
    {p e g : ℕ} (hp : 2 < p)
    (r : ∀ i : Fin e, ZMod (p ^ (i.val + 1)))
    (D : AxisFamilyData p e g)
    (ancestorExposed : ZMod (3 ^ g) → Set (ZMod (p ^ e))) :
    (∀ v, 0 ≤ axisExposedMass (concretePureTowerSurvivor p e r)
      D ancestorExposed v) ∧
    (∑ v : ZMod (3 ^ g),
      axisExposedMass (concretePureTowerSurvivor p e r)
        D ancestorExposed v) ≤
      concreteAxisBudget p e (concretePureTowerSurvivor p e r) ∧
    concreteAxisBudget p e (concretePureTowerSurvivor p e r) <
      1 / ((p : ℝ) - 2) := by
  have hfinite := lemma_5_1_concrete_levelwise_axis_budget (by omega : 0 < p)
    (concretePureTowerSurvivor p e r)
    (concretePureTowerSurvivor_ncard_pos_of_two_lt p e hp r)
    D ancestorExposed
  exact ⟨hfinite.1, hfinite.2, concreteAxisBudget_lt_beta p e hp r⟩

theorem lemma_5_2_exact_skeleton_complement
    {A P : Type*} [Fintype A] [Fintype P]
    (τ : A → ℝ) (q : P → A → ℝ)
    (conditionalComplement : A → ℝ)
    (hindependent : ∀ a, conditionalComplement a = ∏ p, q p a) :
    ∑ a, τ a * (1 - conditionalComplement a) = SkeletonCovered τ q := by
  simp_rw [hindependent]
  rfl

/-- Cardinality form of independence for a finite CRT product: the normalized
size of a product of coordinate complements is the product of their normalized
sizes.  No probabilistic independence hypothesis is needed. -/
theorem finite_crt_product_fraction
    {P : Type*} [Fintype P] [DecidableEq P]
    {X : P → Type*} [∀ p, DecidableEq (X p)]
    (survivor complement : ∀ p, Finset (X p)) :
    ((Finset.univ.pi complement).card : ℝ) /
        (Finset.univ.pi survivor).card =
      ∏ p, ((complement p).card : ℝ) / (survivor p).card := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.card_pi]
  norm_cast

noncomputable def finiteCRTComplementFraction
    {P : Type*} [Fintype P] [DecidableEq P]
    {X : P → Type*} [∀ p, DecidableEq (X p)]
    (survivor complement : ∀ p, Finset (X p)) : ℝ :=
  ((Finset.univ.pi complement).card : ℝ) /
    (Finset.univ.pi survivor).card

/-- Concrete finite-coordinate version of Lemma 5.2.  On every 3-adic leaf,
the set avoiding all exposed axes is an actual dependent Cartesian product;
its cardinal fraction is therefore the exact product of the coordinate
fractions appearing in `SkeletonCovered`. -/
theorem lemma_5_2_finite_crt_skeleton_complement
    {A P : Type*} [Fintype A] [Fintype P] [DecidableEq P]
    {X : P → Type*} [∀ p, DecidableEq (X p)]
    (τ : A → ℝ) (survivor : ∀ p, Finset (X p))
    (complement : ∀ p, A → Finset (X p)) :
    ∑ a, τ a *
        (1 - finiteCRTComplementFraction survivor (fun p => complement p a)) =
      SkeletonCovered τ
        (fun p a => ((complement p a).card : ℝ) / (survivor p).card) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteCRTComplementFraction, finite_crt_product_fraction]

/-! ## Lemma 6.1: residual-family capacity bounds -/

/-- The exact normalized capacity of the 3-adic levels `g = 4,...,e`. -/
noncomputable def threeTailCapacity (e : ℕ) (S : Set (ZMod (3 ^ e))) : ℝ :=
  (∑ i : Fin (e - 3), (3 ^ (e - (i.val + 4)) : ℕ) : ℝ) / S.ncard

/-- Concrete replacement for the tail hypothesis in Lemma 6.1. -/
theorem threeTailCapacity_lt_one_div_twentySeven
    (e : ℕ) (h3 : 3 ≤ e)
    (r : ∀ i : Fin e, ZMod (3 ^ (i.val + 1))) :
    threeTailCapacity e (concretePureTowerSurvivor 3 e r) < 1 / 27 := by
  let A := ∑ i : Fin (e - 3), 3 ^ (e - (i.val + 4))
  let S := concretePureTowerSurvivor 3 e r
  have hA : A = ∑ i : Fin (e - 3), 3 ^ ((e - 3) - (i.val + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  have hgeom : A * 2 + 1 = 3 ^ (e - 3) := by
    rw [hA, reverse_prime_power_sum]
    simpa using (geom_sum_mul_add 2 (e - 3))
  have hpow : 27 * (A * 2 + 1) = 3 ^ e := by
    rw [hgeom, show e = (e - 3) + 3 by omega, pow_add]
    norm_num
    ring
  have hS := concreteThreeTowerSurvivor_ncard_lower e r
  have hodd3 : Odd 3 := ⟨1, by norm_num⟩
  obtain ⟨k, hk⟩ : Odd (3 ^ e) := hodd3.pow
  have hcrossNat : 27 * A < S.ncard := by
    apply lt_of_lt_of_le _ hS
    omega
  have hSposNat : 0 < S.ncard := by omega
  have hSpos : (0 : ℝ) < S.ncard := by exact_mod_cast hSposNat
  unfold threeTailCapacity
  rw [← Nat.cast_sum]
  change (A : ℝ) / (S.ncard : ℝ) < 1 / 27
  rw [div_lt_div_iff₀ hSpos (by norm_num : (0 : ℝ) < 27)]
  norm_num only [one_mul]
  have hc : (((27 * A : ℕ) : ℝ)) < (S.ncard : ℝ) := by
    exact_mod_cast hcrossNat
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hc
  nlinarith

/-- Product of a non-3 exponent-vector capacity and one concrete deep 3-adic
slice capacity. -/
noncomputable def combinedTailCoefficient {E : Type*} [Fintype E]
    (c : E → ℝ) (e : ℕ) (S : Set (ZMod (3 ^ e)))
    (u : E × Fin (e - 3)) : ℝ :=
  c u.1 * ((3 ^ (e - (u.2.val + 4)) : ℕ) : ℝ) / S.ncard

theorem combinedTailCoefficient_sum {E : Type*} [Fintype E]
    (c : E → ℝ) (e : ℕ) (S : Set (ZMod (3 ^ e))) :
    (∑ u : E × Fin (e - 3), combinedTailCoefficient c e S u) =
      (∑ u, c u) * threeTailCapacity e S := by
  rw [Fintype.sum_prod_type]
  simp_rw [combinedTailCoefficient, mul_div_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  unfold threeTailCapacity
  congr 1
  rw [← Finset.sum_div]

theorem combinedTailCoefficient_sum_lt {E : Type*} [Fintype E]
    (c : E → ℝ) (B : ℝ) (hBpos : 0 < B)
    (hbudget : ∑ u, c u ≤ B)
    (e : ℕ) (h3 : 3 ≤ e)
    (r : ∀ i : Fin e, ZMod (3 ^ (i.val + 1))) :
    (∑ u : E × Fin (e - 3), combinedTailCoefficient c e
      (concretePureTowerSurvivor 3 e r) u) < B / 27 := by
  rw [combinedTailCoefficient_sum]
  have htail0 :
      0 ≤ threeTailCapacity e (concretePureTowerSurvivor 3 e r) := by
    unfold threeTailCapacity
    positivity
  have htail := threeTailCapacity_lt_one_div_twentySeven e h3 r
  calc
    (∑ u, c u) * threeTailCapacity e (concretePureTowerSurvivor 3 e r)
      ≤ B * threeTailCapacity e (concretePureTowerSurvivor 3 e r) :=
        mul_le_mul_of_nonneg_right hbudget htail0
    _ < B * (1 / 27) := mul_lt_mul_of_pos_left htail hBpos
    _ = B / 27 := by ring

theorem weighted_capacity_bound
    {E : Type*} [Fintype E]
    (c z : E → ℝ) (B L : ℝ)
    (hc : ∀ e, 0 ≤ c e) (hz : ∀ e, z e ≤ L)
    (hbudget : ∑ e, c e ≤ B) (hL : 0 ≤ L) :
    ∑ e, c e * z e ≤ B * L := by
  calc
    ∑ e, c e * z e ≤ ∑ e, c e * L :=
      Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hz e) (hc e)
    _ = (∑ e, c e) * L := by rw [Finset.sum_mul]
    _ ≤ B * L := mul_le_mul_of_nonneg_right hbudget hL

theorem lemma_6_1_residual_family_bounds
    {E : Type*} [Fintype E]
    (c z0 z1 z2 z3 ztail : E → ℝ)
    (B L0 L1 L2 L3 H : ℝ)
    (hc : ∀ e, 0 ≤ c e) (hbudget : ∑ e, c e ≤ B)
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (hL3 : 0 ≤ L3) (hH : 0 ≤ H)
    (hz0 : ∀ e, z0 e ≤ L0) (hz1 : ∀ e, z1 e ≤ L1)
    (hz2 : ∀ e, z2 e ≤ L2) (hz3 : ∀ e, z3 e ≤ L3)
    (hztail : ∀ e, ztail e ≤ H / 27) :
    (∑ e, c e * z0 e ≤ B * L0) ∧
    (∑ e, c e * z1 e ≤ B * L1) ∧
    (∑ e, c e * z2 e ≤ B * L2) ∧
    (∑ e, c e * z3 e ≤ B * L3) ∧
    (∑ e, c e * ztail e ≤ B / 27 * H) := by
  refine ⟨weighted_capacity_bound c z0 B L0 hc hz0 hbudget hL0,
    weighted_capacity_bound c z1 B L1 hc hz1 hbudget hL1,
    weighted_capacity_bound c z2 B L2 hc hz2 hbudget hL2,
    weighted_capacity_bound c z3 B L3 hc hz3 hbudget hL3, ?_⟩
  convert weighted_capacity_bound c ztail B (H / 27) hc hztail hbudget (by positivity) using 1
  ring

theorem levelZeroResidual_has_atLeastTwoPrimes
    {P : Type*} [DecidableEq P] {T : Finset P}
    (hT : ResidualSupportAtLevel T 0) :
    2 ≤ T.card :=
  hT.2 rfl

/-- Concrete Lemma 6.1 on the rooted `2 × 3 × 3` leaf space.  Placements at
levels one, two, and three are respectively actual branches, nodes, and
leaves.  The tail coefficient has already summed the levels `g ≥ 4`; its
budget is `B/27`. -/
theorem lemma_6_1_concrete_residual_family_bounds
    {P E ETail : Type*} [Fintype P] [DecidableEq P]
    [Fintype E] [Fintype ETail]
    (T : Finset P) (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ)
    (c : E → ℝ) (ctail : ETail → ℝ) (B : ℝ)
    (place1 : E → RootedBranch) (place2 : E → RootedNode)
    (place3 : E → RootedLeaf) (placeTail : ETail → RootedLeaf)
    (hτ : ∀ a, 0 ≤ τ a) (hq : ∀ p a, 0 ≤ q p a)
    (hc : ∀ u, 0 ≤ c u) (hctail : ∀ u, 0 ≤ ctail u)
    (hbudget : ∑ u, c u ≤ B) (htailBudget : ∑ u, ctail u ≤ B / 27) :
    residualContribution0 c τ (residualOutsideProduct T q) ≤
        B * residualL0ForSupport T τ q ∧
    residualContribution1 c place1 τ (residualOutsideProduct T q) ≤
        B * residualL1ForSupport T τ q ∧
    residualContribution2 c place2 τ (residualOutsideProduct T q) ≤
        B * residualL2ForSupport T τ q ∧
    residualContribution3 c place3 τ (residualOutsideProduct T q) ≤
        B * residualL3ForSupport T τ q ∧
    residualTailContribution ctail placeTail (residualOutsideProduct T q) ≤
        B / 27 * residualHForSupport T q := by
  let R := residualOutsideProduct T q
  have hR : ∀ a, 0 ≤ R a := residualOutsideProduct_nonneg T q hq
  have hL0 : 0 ≤ residualL0 τ R := residualL0_nonneg τ R hτ hR
  have hL1 : 0 ≤ residualL1 τ R := residualL1_nonneg τ R hτ hR
  have hL2 : 0 ≤ residualL2 τ R := residualL2_nonneg τ R hτ hR
  have hL3 : 0 ≤ residualL3 τ R := residualL3_nonneg τ R hτ hR
  have hH : 0 ≤ residualH R := residualH_nonneg R hR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact weighted_capacity_bound c (fun _ => residualL0 τ R) B
      (residualL0 τ R) hc (fun _ => le_rfl) hbudget hL0
  · exact weighted_capacity_bound c
      (fun u => ∑ a with leafBranch a = place1 u, τ a * R a) B
      (residualL1 τ R) hc
      (fun u => branchContribution_le_L1 τ R (place1 u)) hbudget hL1
  · exact weighted_capacity_bound c
      (fun u => ∑ a with leafNode a = place2 u, τ a * R a) B
      (residualL2 τ R) hc
      (fun u => nodeContribution_le_L2 τ R (place2 u)) hbudget hL2
  · exact weighted_capacity_bound c
      (fun u => τ (place3 u) * R (place3 u)) B
      (residualL3 τ R) hc
      (fun u => leafContribution_le_L3 τ R (place3 u)) hbudget hL3
  · exact weighted_capacity_bound ctail (fun u => R (placeTail u))
      (B / 27) (residualH R) hctail
      (fun u => residualValue_le_H R (placeTail u)) htailBudget hH

/-- Axis-clipped specialization of concrete Lemma 6.1.  Here `B_T` and
`R_{T,a}` are the displayed products from Section 6, and `q_{p,a}` is computed
from the disjointized level-one, level-two, and promoted level-three masses on
the path to `a`. -/
theorem lemma_6_1_concrete_axis_clipped_bounds
    {P E ETail : Type*} [Fintype P] [DecidableEq P]
    [Fintype E] [Fintype ETail]
    (T promotedLevel3 : Finset P) (β : P → ℝ)
    (τ : RootedLeaf → ℝ) (x : P → RootedAxisExposure)
    (c : E → ℝ) (ctail : ETail → ℝ)
    (place1 : E → RootedBranch) (place2 : E → RootedNode)
    (place3 : E → RootedLeaf) (placeTail : ETail → RootedLeaf)
    (hτ : ∀ a, 0 ≤ τ a)
    (hpath : ∀ p a,
      (x p).level1 (leafBranch a) + (x p).level2 (leafNode a) +
        (if p ∈ promotedLevel3 then (x p).level3 a else 0) ≤ 1)
    (hc : ∀ u, 0 ≤ c u) (hctail : ∀ u, 0 ≤ ctail u)
    (hbudget : ∑ u, c u ≤ residualSupportBudget β T)
    (htailBudget : ∑ u, ctail u ≤ residualSupportBudget β T / 27) :
    let q := axisPathComplement promotedLevel3 x
    residualContribution0 c τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL0ForSupport T τ q ∧
    residualContribution1 c place1 τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL1ForSupport T τ q ∧
    residualContribution2 c place2 τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL2ForSupport T τ q ∧
    residualContribution3 c place3 τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL3ForSupport T τ q ∧
    residualTailContribution ctail placeTail (residualOutsideProduct T q) ≤
        residualSupportBudget β T / 27 * residualHForSupport T q := by
  dsimp only
  exact lemma_6_1_concrete_residual_family_bounds T τ
    (axisPathComplement promotedLevel3 x) c ctail (residualSupportBudget β T)
    place1 place2 place3 placeTail hτ
    (axisPathComplement_nonneg promotedLevel3 x hpath)
    hc hctail hbudget htailBudget

/-- Fully concrete capacity form of Lemma 6.1.  The non-3 coefficient is an
actual product over a dependent exponent vector, its total budget is derived
by `Fintype.prod_sum`, and the deep 3-adic coefficient is the concrete finite
tail whose total is strictly below `B_T/27`. -/
theorem lemma_6_1_fully_concrete_capacity_bounds
    {P : Type*} [Fintype P] [DecidableEq P]
    (T promotedLevel3 : Finset P) (β : P → ℝ) (ep : P → ℕ)
    (cp : ∀ p, Fin (ep p) → ℝ)
    (hcp : ∀ p i, 0 ≤ cp p i)
    (hpBudget : ∀ p : ↥T, ∑ i, cp p i ≤ β p)
    (hβpos : ∀ p ∈ T, 0 < β p)
    (e3 : ℕ) (h3 : 3 ≤ e3)
    (r3 : ∀ i : Fin e3, ZMod (3 ^ (i.val + 1)))
    (τ : RootedLeaf → ℝ) (x : P → RootedAxisExposure)
    (place1 : SupportExponentVector T ep → RootedBranch)
    (place2 : SupportExponentVector T ep → RootedNode)
    (place3 : SupportExponentVector T ep → RootedLeaf)
    (placeTail : (SupportExponentVector T ep × Fin (e3 - 3)) → RootedLeaf)
    (hτ : ∀ a, 0 ≤ τ a)
    (hpath : ∀ p a,
      (x p).level1 (leafBranch a) + (x p).level2 (leafNode a) +
        (if p ∈ promotedLevel3 then (x p).level3 a else 0) ≤ 1) :
    let c := exponentVectorCapacity T ep cp
    let S3 := concretePureTowerSurvivor 3 e3 r3
    let ctail := combinedTailCoefficient c e3 S3
    let q := axisPathComplement promotedLevel3 x
    residualContribution0 c τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL0ForSupport T τ q ∧
    residualContribution1 c place1 τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL1ForSupport T τ q ∧
    residualContribution2 c place2 τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL2ForSupport T τ q ∧
    residualContribution3 c place3 τ (residualOutsideProduct T q) ≤
        residualSupportBudget β T * residualL3ForSupport T τ q ∧
    residualTailContribution ctail placeTail (residualOutsideProduct T q) ≤
        residualSupportBudget β T / 27 * residualHForSupport T q := by
  dsimp only
  let c := exponentVectorCapacity T ep cp
  let S3 := concretePureTowerSurvivor 3 e3 r3
  have hc : ∀ u, 0 ≤ c u :=
    fun u => exponentVectorCapacity_nonneg T ep cp hcp u
  have hbudget : ∑ u, c u ≤ residualSupportBudget β T :=
    exponentVectorCapacity_sum_le_supportBudget T ep cp β hcp hpBudget
  have hBpos : 0 < residualSupportBudget β T :=
    residualSupportBudget_pos T β hβpos
  have htailBudget :
      ∑ u : SupportExponentVector T ep × Fin (e3 - 3),
          combinedTailCoefficient c e3 S3 u ≤ residualSupportBudget β T / 27 :=
    le_of_lt (combinedTailCoefficient_sum_lt c (residualSupportBudget β T)
      hBpos hbudget e3 h3 r3)
  have hctail : ∀ u : SupportExponentVector T ep × Fin (e3 - 3),
      0 ≤ combinedTailCoefficient c e3 S3 u := by
    intro u
    unfold combinedTailCoefficient
    exact div_nonneg (mul_nonneg (hc u.1) (by positivity)) (by positivity)
  exact lemma_6_1_concrete_axis_clipped_bounds T promotedLevel3 β τ x
    c (combinedTailCoefficient c e3 S3) place1 place2 place3 placeTail
    hτ hpath hc hctail hbudget htailBudget

/-! ## Lemmas 7.1--7.4: convexity, vertices, symmetry, promotion -/

theorem convexOn_finset_sum
    {E I : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (t : Finset I) (f : I → E → ℝ)
    (hs : Convex ℝ s)
    (hf : ∀ i ∈ t, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using convexOn_const (𝕜 := ℝ) (s := s) (0 : ℝ) hs
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a t)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem lemma_7_1_separate_convexity
    {E I : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (affinePart : E → ℝ) (clips : I → E → ℝ) (t : Finset I)
    (hs : Convex ℝ s)
    (haffine : ConvexOn ℝ s affinePart)
    (hclips : ∀ i ∈ t, ConvexOn ℝ s (clips i)) :
    ConvexOn ℝ s (fun x => affinePart x + ∑ i ∈ t, clips i x) := by
  exact haffine.add (convexOn_finset_sum t clips hs hclips)

/-- The complete Stage-I/Stage-II formula is convex in the rooted 3-adic
profile when all concrete axis blocks are fixed. -/
theorem lemma_7_1_concrete_profile_convexity
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) (β : P → ℝ) (x : P → RootedAxisExposure)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s)
    (hβ0 : ∀ p, 0 ≤ β p) :
    ConvexOn ℝ s (fun τ => clippedStageFunctional promoted β τ x) := by
  let q := axisPathComplement promoted x
  have hB0 (T : Finset P) : 0 ≤ residualSupportBudget β T := by
    exact Finset.prod_nonneg fun p hp => hβ0 p
  have hskel : ConvexOn ℝ s (fun τ => SkeletonCovered τ q) := by
    simpa [SkeletonCovered] using
      (weightedSum_convexOn (fun a => 1 - ∏ p, q p a) hs)
  have hmulti (T : Finset P) : ConvexOn ℝ s (fun τ =>
      residualSupportBudget β T *
        (residualL0ForSupport T τ q + residualL1ForSupport T τ q +
          residualL2ForSupport T τ q + residualL3ForSupport T τ q)) := by
    have h0 : ConvexOn ℝ s (fun τ => residualL0ForSupport T τ q) := by
      simpa [residualL0ForSupport, residualL0] using
        (weightedSum_convexOn (residualOutsideProduct T q) hs)
    have h1 := residualL1_convexOn (residualOutsideProduct T q) hs
    have h2 := residualL2_convexOn (residualOutsideProduct T q) hs
    have h3 := residualL3_convexOn (residualOutsideProduct T q) hs
    have hadd := ((h0.add h1).add h2).add h3
    simpa [residualL1ForSupport, residualL2ForSupport, residualL3ForSupport,
      smul_eq_mul] using hadd.smul (hB0 T)
  have hsingle (p : P) : ConvexOn ℝ s (fun τ =>
      residualSupportBudget β {p} * residualL3ForSupport {p} τ q) := by
    have h3 := residualL3_convexOn (residualOutsideProduct {p} q) hs
    simpa [residualL3ForSupport, smul_eq_mul] using h3.smul (hB0 {p})
  have htail (T : Finset P) : ConvexOn ℝ s (fun _ : RootedLeaf → ℝ =>
      residualSupportBudget β T / 27 * residualHForSupport T q) :=
    convexOn_const (𝕜 := ℝ) _ hs
  have hm := convexOn_finset_sum (multiPrimeSupports P)
    (fun T τ => residualSupportBudget β T *
      (residualL0ForSupport T τ q + residualL1ForSupport T τ q +
        residualL2ForSupport T τ q + residualL3ForSupport T τ q)) hs
    (fun T hT => hmulti T)
  have hsng := convexOn_finset_sum (Finset.univ.filter fun p => p ∉ promoted)
    (fun p τ => residualSupportBudget β {p} * residualL3ForSupport {p} τ q) hs
    (fun p hp => hsingle p)
  have ht := convexOn_finset_sum (nonemptySupports P)
    (fun T _ => residualSupportBudget β T / 27 * residualHForSupport T q) hs
    (fun T hT => htail T)
  simpa [clippedStageFunctional, q] using ((hskel.add hm).add hsng).add ht

/-- The complete Stage-I/Stage-II formula is convex in each concrete
per-prime path-complement block when the profile and all other prime blocks
are fixed.  This is the axis-block half of the separate-convexity reduction. -/
theorem lemma_7_1_concrete_axis_block_convexity
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) (β : P → ℝ) (τ : RootedLeaf → ℝ)
    (q : P → RootedLeaf → ℝ) (p : P)
    {s : Set (RootedLeaf → ℝ)} (hs : Convex ℝ s)
    (hβ0 : ∀ r, 0 ≤ β r) :
    ConvexOn ℝ s (fun z =>
      clippedFunctionalFromQ promoted β τ (replaceQCoordinate q p z)) := by
  have hB0 (T : Finset P) : 0 ≤ residualSupportBudget β T := by
    exact Finset.prod_nonneg fun r hr => hβ0 r
  have hskel := skeleton_qblock_convexOn τ q p hs
  have hmulti (T : Finset P) : ConvexOn ℝ s (fun z =>
      residualSupportBudget β T *
        (residualL0ForSupport T τ (replaceQCoordinate q p z) +
          residualL1ForSupport T τ (replaceQCoordinate q p z) +
          residualL2ForSupport T τ (replaceQCoordinate q p z) +
          residualL3ForSupport T τ (replaceQCoordinate q p z))) := by
    have h0 := residualL0_qblock_convexOn τ T q p hs
    have h1 := residualL1_qblock_convexOn τ T q p hs
    have h2 := residualL2_qblock_convexOn τ T q p hs
    have h3 := residualL3_qblock_convexOn τ T q p hs
    simpa [smul_eq_mul] using (((h0.add h1).add h2).add h3).smul (hB0 T)
  have hsingle (r : P) : ConvexOn ℝ s (fun z =>
      residualSupportBudget β {r} *
        residualL3ForSupport {r} τ (replaceQCoordinate q p z)) := by
    have h3 := residualL3_qblock_convexOn τ {r} q p hs
    simpa [smul_eq_mul] using h3.smul (hB0 {r})
  have htail (T : Finset P) : ConvexOn ℝ s (fun z =>
      residualSupportBudget β T / 27 *
        residualHForSupport T (replaceQCoordinate q p z)) := by
    have hH := residualH_qblock_convexOn T q p hs
    have hcoeff : 0 ≤ residualSupportBudget β T / 27 :=
      div_nonneg (hB0 T) (by norm_num)
    simpa [smul_eq_mul] using hH.smul hcoeff
  have hm := convexOn_finset_sum (multiPrimeSupports P)
    (fun T z => residualSupportBudget β T *
      (residualL0ForSupport T τ (replaceQCoordinate q p z) +
        residualL1ForSupport T τ (replaceQCoordinate q p z) +
        residualL2ForSupport T τ (replaceQCoordinate q p z) +
        residualL3ForSupport T τ (replaceQCoordinate q p z))) hs
    (fun T hT => hmulti T)
  have hsng := convexOn_finset_sum (Finset.univ.filter fun r => r ∉ promoted)
    (fun r z => residualSupportBudget β {r} *
      residualL3ForSupport {r} τ (replaceQCoordinate q p z)) hs
    (fun r hr => hsingle r)
  have ht := convexOn_finset_sum (nonemptySupports P)
    (fun T z => residualSupportBudget β T / 27 *
      residualHForSupport T (replaceQCoordinate q p z)) hs
    (fun T hT => htail T)
  simpa [clippedFunctionalFromQ] using ((hskel.add hm).add hsng).add ht

theorem lemma_7_2_vertex_reduction_two_blocks
    {X Y : Type*} (F : X → Y → ℝ) (VX : Set X) (VY : Set Y)
    (hx : ∀ x y, ∃ vx ∈ VX, F x y ≤ F vx y)
    (hy : ∀ vx ∈ VX, ∀ y, ∃ vy ∈ VY, F vx y ≤ F vx vy) :
    ∀ x y, ∃ vx ∈ VX, ∃ vy ∈ VY, F x y ≤ F vx vy := by
  intro x y
  obtain ⟨vx, hvx, hxy⟩ := hx x y
  obtain ⟨vy, hvy, hyv⟩ := hy vx hvx y
  exact ⟨vx, hvx, vy, hvy, hxy.trans hyv⟩

theorem lemma_7_3_rooted_tree_symmetry_sum
    {I : Type*} [Fintype I] (σ : I ≃ I) (f : I → ℝ) :
    ∑ i, f (σ i) = ∑ i, f i := σ.sum_comp f

theorem lemma_7_3_rooted_tree_symmetry_product
    {I : Type*} [Fintype I] (σ : I ≃ I) (f : I → ℝ) :
    ∏ i, f (σ i) = ∏ i, f i := σ.prod_comp f

/-! The concrete `2 × 3 × 3` tree.  Sorting at each node quotients exactly the
independent sibling permutations: first the three leaves, then the three
depth-two nodes, and finally the two live branches. -/

abbrev DiscreteProfile := RootedLeaf → Fin 3

def discreteProfileOf (zeros : Finset RootedLeaf) (one : RootedLeaf) :
    DiscreteProfile :=
  fun i => if i ∈ zeros then 0 else if i = one then 1 else 2

def positionalEncode (base : ℕ) (xs : List ℕ) : ℕ :=
  xs.foldl (fun acc x => acc * base + x) 0

def sortNat (xs : List ℕ) : List ℕ :=
  xs.mergeSort fun a b => decide (a ≤ b)

def rootedNodeCode (w : DiscreteProfile) (b : Fin 2) (n : Fin 3) : ℕ :=
  positionalEncode 3
    (sortNat (List.ofFn fun l : Fin 3 => (w (b, n, l)).val))

def rootedBranchCode (w : DiscreteProfile) (b : Fin 2) : ℕ :=
  positionalEncode 27
    (sortNat (List.ofFn fun n : Fin 3 => rootedNodeCode w b n))

def rootedCanonicalKey (w : DiscreteProfile) : ℕ :=
  positionalEncode (27 ^ 3)
    (sortNat (List.ofFn fun b : Fin 2 => rootedBranchCode w b))

/-- Canonical keys of all labelled profiles having four zero leaves, one
unit leaf, and thirteen leaves of value two. -/
def rootedCanonicalKeys : Finset ℕ :=
  Finset.univ.powersetCard 4 |>.biUnion fun zeros =>
    (Finset.univ \ zeros).image fun one =>
      rootedCanonicalKey (discreteProfileOf zeros one)

theorem lemma_7_3_rooted_tree_orbit_count : rootedCanonicalKeys.card = 28 := by
  native_decide

theorem lemma_7_4_promotion
    {A : Type*} [Fintype A]
    (τ y R : A → ℝ) (B L : ℝ)
    (hy : ∀ a, 0 ≤ y a) (hbudget : ∑ a, y a ≤ B)
    (hclip : ∀ a, τ a * R a ≤ L) (hL : 0 ≤ L) :
    ∑ a, τ a * y a * R a ≤ B * L := by
  calc
    ∑ a, τ a * y a * R a = ∑ a, y a * (τ a * R a) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a, y a * L :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hclip a) (hy a)
    _ = (∑ a, y a) * L := by rw [Finset.sum_mul]
    _ ≤ B * L := mul_le_mul_of_nonneg_right hbudget hL

/-- Concrete promotion-cost inequality for a singleton axis.  The clipping
factor is the actual product over all coordinates outside `{p}`, and the old
residual allowance is exactly `β_p L₃({p})`. -/
theorem lemma_7_4_concrete_singleton_promotion_cost
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) (p : P) (β : P → ℝ)
    (τ : RootedLeaf → ℝ) (x : P → RootedAxisExposure)
    (y : RootedLeaf → ℝ)
    (hτ : ∀ a, 0 ≤ τ a)
    (hpath : ∀ r a,
      (x r).level1 (leafBranch a) + (x r).level2 (leafNode a) +
        (if r ∈ promoted then (x r).level3 a else 0) ≤ 1)
    (hy : ∀ a, 0 ≤ y a) (hbudget : ∑ a, y a ≤ β p) :
    let q := axisPathComplement promoted x
    ∑ a, τ a * y a * residualOutsideProduct {p} q a ≤
      β p * residualL3ForSupport {p} τ q := by
  dsimp only
  let q := axisPathComplement promoted x
  let R := residualOutsideProduct {p} q
  have hq : ∀ r a, 0 ≤ q r a := axisPathComplement_nonneg promoted x hpath
  have hR : ∀ a, 0 ≤ R a := residualOutsideProduct_nonneg {p} q hq
  exact lemma_7_4_promotion τ y R (β p) (residualL3 τ R) hy hbudget
    (fun a => leafContribution_le_L3 τ R a)
    (residualL3_nonneg τ R hτ hR)

/-! ## Lemma 8.1: budget monotonicity -/

noncomputable def RelaxationMaximum {X : Type*} (domain : Set X) (F : X → ℝ) : ℝ :=
  sSup (F '' domain)

theorem lemma_8_1_budget_monotonicity
    {X : Type*} {small large : Set X} {Fsmall Flarge : X → ℝ}
    (hne : small.Nonempty) (hsub : small ⊆ large)
    (hmono : ∀ x ∈ small, Fsmall x ≤ Flarge x)
    (hbounded : BddAbove (Flarge '' large)) :
    RelaxationMaximum small Fsmall ≤ RelaxationMaximum large Flarge := by
  apply csSup_le
  · exact hne.image Fsmall
  · rintro y ⟨x, hx, rfl⟩
    exact (hmono x hx).trans (le_csSup hbounded ⟨x, hsub hx, rfl⟩)

/-- Concrete budget monotonicity for the complete Stage-I/Stage-II functional
and its product of the rooted profile polytope with all axis simplices. -/
theorem lemma_8_1_concrete_budget_monotonicity
    {P : Type*} [Fintype P] [DecidableEq P]
    (promoted : Finset P) {β β' : P → ℝ}
    (hβ0 : ∀ p, 0 ≤ β p) (hβ : ∀ p, β p ≤ β' p)
    (hne : (concreteRelaxationDomain promoted β).Nonempty)
    (hbounded : BddAbove
      (concreteRelaxationValue promoted β' ''
        concreteRelaxationDomain promoted β')) :
    RelaxationMaximum (concreteRelaxationDomain promoted β)
        (concreteRelaxationValue promoted β) ≤
      RelaxationMaximum (concreteRelaxationDomain promoted β')
        (concreteRelaxationValue promoted β') := by
  apply lemma_8_1_budget_monotonicity hne
    (concreteRelaxationDomain_mono promoted hβ)
  · intro z hz
    exact clippedStageFunctional_mono_budget promoted z.profile z.axis β β'
      (fun a => (hz.1.1 a).1)
      (fun p a => (hz.2 p).2.2.2.2.2.2 a) hβ0 hβ
  · exact hbounded

end SevenPrime
