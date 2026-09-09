import SevenPrime.AxisResidual

namespace SevenPrime
open scoped BigOperators

theorem finiteSup_reindex {J : Type*} [Fintype J] [Nonempty J]
    (σ : Equiv.Perm J) (f : J → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j => f (σ.symm j)) =
      Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro j hj
    exact Finset.le_sup' f (Finset.mem_univ (σ.symm j))
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro j hj
    simpa using Finset.le_sup' (fun k => f (σ.symm k))
      (Finset.mem_univ (σ j))

structure RootedTreeAutomorphism where
  leafPerm : Equiv.Perm RootedLeaf
  branchPerm : Equiv.Perm RootedBranch
  nodePerm : Equiv.Perm RootedNode
  map_branch : ∀ a, leafBranch (leafPerm a) = branchPerm (leafBranch a)
  map_node : ∀ a, leafNode (leafPerm a) = nodePerm (leafNode a)

def relabelLeaf (σ : RootedTreeAutomorphism) (f : RootedLeaf → ℝ) :
    RootedLeaf → ℝ := fun a => f (σ.leafPerm.symm a)

def relabelQ {P : Type*} (σ : RootedTreeAutomorphism)
    (q : P → RootedLeaf → ℝ) : P → RootedLeaf → ℝ :=
  fun p => relabelLeaf σ (q p)

theorem relabelLeaf_apply_perm (σ : RootedTreeAutomorphism)
    (f : RootedLeaf → ℝ) (a : RootedLeaf) :
    relabelLeaf σ f (σ.leafPerm a) = f a := by
  simp [relabelLeaf]

theorem residualOutsideProduct_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (T : Finset P)
    (q : P → RootedLeaf → ℝ) (a : RootedLeaf) :
    residualOutsideProduct T (relabelQ σ q) a =
      residualOutsideProduct T q (σ.leafPerm.symm a) := by
  simp [residualOutsideProduct, relabelQ, relabelLeaf]

theorem residualL0_relabel (σ : RootedTreeAutomorphism)
    (τ R : RootedLeaf → ℝ) :
    residualL0 (relabelLeaf σ τ) (relabelLeaf σ R) = residualL0 τ R := by
  unfold residualL0
  calc
    (∑ a, relabelLeaf σ τ a * relabelLeaf σ R a) =
        ∑ a, (relabelLeaf σ τ (σ.leafPerm a) *
          relabelLeaf σ R (σ.leafPerm a)) := by
      exact (Equiv.sum_comp σ.leafPerm
        (fun a => relabelLeaf σ τ a * relabelLeaf σ R a)).symm
    _ = ∑ a, τ a * R a := by simp [relabelLeaf]

theorem branchContribution_relabel (σ : RootedTreeAutomorphism)
    (τ R : RootedLeaf → ℝ) (b : RootedBranch) :
    (∑ a with leafBranch a = b,
      relabelLeaf σ τ a * relabelLeaf σ R a) =
      ∑ a with leafBranch a = σ.branchPerm.symm b, τ a * R a := by
  simp only [Finset.sum_filter]
  calc
    (∑ a, if leafBranch a = b then
        relabelLeaf σ τ a * relabelLeaf σ R a else 0) =
      ∑ a, if leafBranch (σ.leafPerm a) = b then
        relabelLeaf σ τ (σ.leafPerm a) *
          relabelLeaf σ R (σ.leafPerm a) else 0 := by
        exact (Equiv.sum_comp σ.leafPerm (fun a => if leafBranch a = b then
          relabelLeaf σ τ a * relabelLeaf σ R a else 0)).symm
    _ = ∑ a, if leafBranch a = σ.branchPerm.symm b then τ a * R a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [σ.map_branch]
      simp only [relabelLeaf_apply_perm]
      by_cases h : leafBranch a = σ.branchPerm.symm b
      · simp [h]
      · have hn : σ.branchPerm (leafBranch a) ≠ b := by
          intro he
          apply h
          exact σ.branchPerm.injective (by simpa using he)
        simp [h, hn]

theorem nodeContribution_relabel (σ : RootedTreeAutomorphism)
    (τ R : RootedLeaf → ℝ) (v : RootedNode) :
    (∑ a with leafNode a = v,
      relabelLeaf σ τ a * relabelLeaf σ R a) =
      ∑ a with leafNode a = σ.nodePerm.symm v, τ a * R a := by
  simp only [Finset.sum_filter]
  calc
    (∑ a, if leafNode a = v then
        relabelLeaf σ τ a * relabelLeaf σ R a else 0) =
      ∑ a, if leafNode (σ.leafPerm a) = v then
        relabelLeaf σ τ (σ.leafPerm a) *
          relabelLeaf σ R (σ.leafPerm a) else 0 := by
        exact (Equiv.sum_comp σ.leafPerm (fun a => if leafNode a = v then
          relabelLeaf σ τ a * relabelLeaf σ R a else 0)).symm
    _ = ∑ a, if leafNode a = σ.nodePerm.symm v then τ a * R a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [σ.map_node]
      simp only [relabelLeaf_apply_perm]
      by_cases h : leafNode a = σ.nodePerm.symm v
      · simp [h]
      · have hn : σ.nodePerm (leafNode a) ≠ v := by
          intro he
          apply h
          exact σ.nodePerm.injective (by simpa using he)
        simp [h, hn]

theorem residualL1_relabel (σ : RootedTreeAutomorphism)
    (τ R : RootedLeaf → ℝ) :
    residualL1 (relabelLeaf σ τ) (relabelLeaf σ R) = residualL1 τ R := by
  unfold residualL1
  rw [show (fun b : RootedBranch => ∑ a with leafBranch a = b,
      relabelLeaf σ τ a * relabelLeaf σ R a) =
      (fun b => ∑ a with leafBranch a = σ.branchPerm.symm b, τ a * R a) by
    funext b
    exact branchContribution_relabel σ τ R b]
  exact finiteSup_reindex σ.branchPerm
    (fun b => ∑ a with leafBranch a = b, τ a * R a)

theorem residualL2_relabel (σ : RootedTreeAutomorphism)
    (τ R : RootedLeaf → ℝ) :
    residualL2 (relabelLeaf σ τ) (relabelLeaf σ R) = residualL2 τ R := by
  unfold residualL2
  rw [show (fun v : RootedNode => ∑ a with leafNode a = v,
      relabelLeaf σ τ a * relabelLeaf σ R a) =
      (fun v => ∑ a with leafNode a = σ.nodePerm.symm v, τ a * R a) by
    funext v
    exact nodeContribution_relabel σ τ R v]
  exact finiteSup_reindex σ.nodePerm
    (fun v => ∑ a with leafNode a = v, τ a * R a)

theorem residualL3_relabel (σ : RootedTreeAutomorphism)
    (τ R : RootedLeaf → ℝ) :
    residualL3 (relabelLeaf σ τ) (relabelLeaf σ R) = residualL3 τ R := by
  unfold residualL3
  rw [show (fun a : RootedLeaf => relabelLeaf σ τ a * relabelLeaf σ R a) =
      (fun a => τ (σ.leafPerm.symm a) * R (σ.leafPerm.symm a)) by
    rfl]
  exact finiteSup_reindex σ.leafPerm (fun a => τ a * R a)

theorem residualH_relabel (σ : RootedTreeAutomorphism) (R : RootedLeaf → ℝ) :
    residualH (relabelLeaf σ R) = residualH R := by
  unfold residualH
  exact finiteSup_reindex σ.leafPerm R

theorem SkeletonCovered_relabel
    {P : Type*} [Fintype P]
    (σ : RootedTreeAutomorphism) (τ : RootedLeaf → ℝ)
    (q : P → RootedLeaf → ℝ) :
    SkeletonCovered (relabelLeaf σ τ) (relabelQ σ q) = SkeletonCovered τ q := by
  unfold SkeletonCovered
  calc
    (∑ a, relabelLeaf σ τ a * (1 - ∏ p, relabelQ σ q p a)) =
        ∑ a, relabelLeaf σ τ (σ.leafPerm a) *
          (1 - ∏ p, relabelQ σ q p (σ.leafPerm a)) := by
      exact (Equiv.sum_comp σ.leafPerm (fun a =>
        relabelLeaf σ τ a * (1 - ∏ p, relabelQ σ q p a))).symm
    _ = ∑ a, τ a * (1 - ∏ p, q p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [relabelQ, relabelLeaf]

theorem residualL0ForSupport_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (T : Finset P)
    (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) :
    residualL0ForSupport T (relabelLeaf σ τ) (relabelQ σ q) =
      residualL0ForSupport T τ q := by
  unfold residualL0ForSupport
  rw [show residualOutsideProduct T (relabelQ σ q) =
      relabelLeaf σ (residualOutsideProduct T q) by
    funext a
    exact residualOutsideProduct_relabel σ T q a]
  exact residualL0_relabel σ τ (residualOutsideProduct T q)

theorem residualL1ForSupport_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (T : Finset P)
    (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) :
    residualL1ForSupport T (relabelLeaf σ τ) (relabelQ σ q) =
      residualL1ForSupport T τ q := by
  unfold residualL1ForSupport
  rw [show residualOutsideProduct T (relabelQ σ q) =
      relabelLeaf σ (residualOutsideProduct T q) by
    funext a
    exact residualOutsideProduct_relabel σ T q a]
  exact residualL1_relabel σ τ (residualOutsideProduct T q)

theorem residualL2ForSupport_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (T : Finset P)
    (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) :
    residualL2ForSupport T (relabelLeaf σ τ) (relabelQ σ q) =
      residualL2ForSupport T τ q := by
  unfold residualL2ForSupport
  rw [show residualOutsideProduct T (relabelQ σ q) =
      relabelLeaf σ (residualOutsideProduct T q) by
    funext a
    exact residualOutsideProduct_relabel σ T q a]
  exact residualL2_relabel σ τ (residualOutsideProduct T q)

theorem residualL3ForSupport_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (T : Finset P)
    (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) :
    residualL3ForSupport T (relabelLeaf σ τ) (relabelQ σ q) =
      residualL3ForSupport T τ q := by
  unfold residualL3ForSupport
  rw [show residualOutsideProduct T (relabelQ σ q) =
      relabelLeaf σ (residualOutsideProduct T q) by
    funext a
    exact residualOutsideProduct_relabel σ T q a]
  exact residualL3_relabel σ τ (residualOutsideProduct T q)

theorem residualHForSupport_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (T : Finset P)
    (q : P → RootedLeaf → ℝ) :
    residualHForSupport T (relabelQ σ q) = residualHForSupport T q := by
  unfold residualHForSupport
  rw [show residualOutsideProduct T (relabelQ σ q) =
      relabelLeaf σ (residualOutsideProduct T q) by
    funext a
    exact residualOutsideProduct_relabel σ T q a]
  exact residualH_relabel σ (residualOutsideProduct T q)

theorem clippedFunctionalFromQ_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (promoted : Finset P) (β : P → ℝ)
    (τ : RootedLeaf → ℝ) (q : P → RootedLeaf → ℝ) :
    clippedFunctionalFromQ promoted β (relabelLeaf σ τ) (relabelQ σ q) =
      clippedFunctionalFromQ promoted β τ q := by
  unfold clippedFunctionalFromQ
  rw [SkeletonCovered_relabel]
  simp_rw [residualL0ForSupport_relabel σ, residualL1ForSupport_relabel σ,
    residualL2ForSupport_relabel σ, residualL3ForSupport_relabel σ,
    residualHForSupport_relabel σ]

/-- Transport all three levels of an axis exposure along a rooted-tree
automorphism. -/
def relabelAxisExposure (σ : RootedTreeAutomorphism)
    (x : RootedAxisExposure) : RootedAxisExposure where
  level1 b := x.level1 (σ.branchPerm.symm b)
  level2 v := x.level2 (σ.nodePerm.symm v)
  level3 a := x.level3 (σ.leafPerm.symm a)

theorem branch_symm_compat (σ : RootedTreeAutomorphism) (a : RootedLeaf) :
    σ.branchPerm.symm (leafBranch a) = leafBranch (σ.leafPerm.symm a) := by
  apply σ.branchPerm.injective
  simpa using σ.map_branch (σ.leafPerm.symm a)

theorem node_symm_compat (σ : RootedTreeAutomorphism) (a : RootedLeaf) :
    σ.nodePerm.symm (leafNode a) = leafNode (σ.leafPerm.symm a) := by
  apply σ.nodePerm.injective
  simpa using σ.map_node (σ.leafPerm.symm a)

theorem axisPathComplement_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (promoted : Finset P)
    (x : P → RootedAxisExposure) :
    axisPathComplement promoted (fun p => relabelAxisExposure σ (x p)) =
      relabelQ σ (axisPathComplement promoted x) := by
  funext p a
  unfold axisPathComplement relabelQ relabelLeaf
  simp only [relabelAxisExposure]
  rw [branch_symm_compat, node_symm_compat]

/-- Invariance of the actual Stage-I/Stage-II functional, stated in its
original exposure variables rather than only in the derived `q` blocks. -/
theorem clippedStageFunctional_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (promoted : Finset P) (β : P → ℝ)
    (τ : RootedLeaf → ℝ) (x : P → RootedAxisExposure) :
    clippedStageFunctional promoted β (relabelLeaf σ τ)
        (fun p => relabelAxisExposure σ (x p)) =
      clippedStageFunctional promoted β τ x := by
  unfold clippedStageFunctional
  rw [axisPathComplement_relabel]
  exact clippedFunctionalFromQ_relabel σ promoted β τ
    (axisPathComplement promoted x)

theorem rootedProfilePolytope_relabel (σ : RootedTreeAutomorphism)
    (τ : RootedLeaf → ℝ) (hτ : RootedProfilePolytope τ) :
    RootedProfilePolytope (relabelLeaf σ τ) := by
  constructor
  · intro a
    exact hτ.1 (σ.leafPerm.symm a)
  · calc
      (∑ a, relabelLeaf σ τ a) = ∑ a, τ a := by
        simpa [relabelLeaf] using Equiv.sum_comp σ.leafPerm.symm τ
      _ = 1 := hτ.2

theorem axisExposureFeasible_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (promoted : Finset P) (β : P → ℝ)
    (x : P → RootedAxisExposure) (hx : AxisExposureFeasible promoted β x) :
    AxisExposureFeasible promoted β
      (fun p => relabelAxisExposure σ (x p)) := by
  intro p
  obtain ⟨h1, h2, h3, hb1, hb2, hb3, hpath⟩ := hx p
  refine ⟨fun b => h1 (σ.branchPerm.symm b),
    fun v => h2 (σ.nodePerm.symm v),
    fun a => h3 (σ.leafPerm.symm a), ?_, ?_, ?_, ?_⟩
  · simpa [relabelAxisExposure] using
      (Equiv.sum_comp σ.branchPerm.symm (x p).level1).le.trans hb1
  · simpa [relabelAxisExposure] using
      (Equiv.sum_comp σ.nodePerm.symm (x p).level2).le.trans hb2
  · simpa [relabelAxisExposure] using
      (Equiv.sum_comp σ.leafPerm.symm (x p).level3).le.trans hb3
  · intro a
    dsimp [relabelAxisExposure]
    rw [branch_symm_compat, node_symm_compat]
    exact hpath (σ.leafPerm.symm a)

def relabelConcreteRelaxationPoint {P : Type*}
    (σ : RootedTreeAutomorphism) (z : ConcreteRelaxationPoint P) :
    ConcreteRelaxationPoint P where
  profile := relabelLeaf σ z.profile
  axis p := relabelAxisExposure σ (z.axis p)

theorem concreteRelaxationDomain_relabel
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (promoted : Finset P) (β : P → ℝ)
    (z : ConcreteRelaxationPoint P)
    (hz : z ∈ concreteRelaxationDomain promoted β) :
    relabelConcreteRelaxationPoint σ z ∈ concreteRelaxationDomain promoted β := by
  exact ⟨rootedProfilePolytope_relabel σ z.profile hz.1,
    axisExposureFeasible_relabel σ promoted β z.axis hz.2⟩

/-- Lemma 7.3 in the concrete relaxation: a rooted-tree automorphism preserves
both feasibility and the value of the complete Stage-I/Stage-II objective. -/
theorem lemma_7_3_concrete_rooted_tree_invariance
    {P : Type*} [Fintype P] [DecidableEq P]
    (σ : RootedTreeAutomorphism) (promoted : Finset P) (β : P → ℝ)
    (z : ConcreteRelaxationPoint P) :
    concreteRelaxationValue promoted β (relabelConcreteRelaxationPoint σ z) =
      concreteRelaxationValue promoted β z := by
  exact clippedStageFunctional_relabel σ promoted β z.profile z.axis

end SevenPrime
