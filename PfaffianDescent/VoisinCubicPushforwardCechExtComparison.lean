import PfaffianDescent.VoisinCubicPushforwardExtVanishing
import PfaffianDescent.VoisinCubicPushforwardRawCech
import PfaffianDescent.VoisinCubicRestrictionBoundary

/-!
# Degree-two Cech-to-Ext comparison for a pushed-forward cubic twist

The standard ambient coordinate-cover Cech complex computes degree-two
cohomology of `i_* O_S(-m)`.  The proof uses the section-representer
resolution and the local Ext vanishings proved from the cubic restriction
sequence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

noncomputable abbrev cubicPushforwardTwist
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) :
    (Proj PS).Modules :=
  (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
    (sheafOfModules (grading (equationIdeal p hp)) m)

/-- Yoneda identifies Hom from the ambient section-representer Cech term
with the corresponding raw ambient-pushforward Cech term. -/
noncomputable def cubicPushforwardSectionRepresenterCechHomEquiv
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ) :
    ((p3SectionRepresenterCechChain K).X n ⟶
        cubicPushforwardTwist K p hp m) ≃
      (cubicPushforwardNegativeTwistCechComplex K p hp m).X n :=
  smallCoverSectionHomEquiv (Proj PS).ringCatSheaf (p3StandardOpen K)
    (cubicPushforwardTwist K p hp m) n

lemma cubicPushforwardSectionRepresenterCechHomEquiv_zero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ) :
    cubicPushforwardSectionRepresenterCechHomEquiv K p hp m n 0 = 0 :=
  smallCoverSectionHomEquiv_zero (Proj PS).ringCatSheaf (p3StandardOpen K)
    (cubicPushforwardTwist K p hp m) n

lemma cubicPushforwardSectionRepresenterCechHomEquiv_add
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ)
    (x y : (p3SectionRepresenterCechChain K).X n ⟶
      cubicPushforwardTwist K p hp m) :
    cubicPushforwardSectionRepresenterCechHomEquiv K p hp m n (x + y) =
      cubicPushforwardSectionRepresenterCechHomEquiv K p hp m n x +
        cubicPushforwardSectionRepresenterCechHomEquiv K p hp m n y :=
  smallCoverSectionHomEquiv_add (Proj PS).ringCatSheaf (p3StandardOpen K)
    (cubicPushforwardTwist K p hp m) n x y

lemma cubicPushforwardSectionRepresenterCechHomEquiv_d
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ)
    (h : (p3SectionRepresenterCechChain K).X n ⟶
      cubicPushforwardTwist K p hp m) :
    cubicPushforwardSectionRepresenterCechHomEquiv K p hp m (n + 1)
        ((p3SectionRepresenterCechChain K).d (n + 1) n ≫ h) =
      (cubicPushforwardNegativeTwistCechComplex K p hp m).d n (n + 1)
        (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m n h) :=
  smallCoverSectionHomEquiv_d (Proj PS).ringCatSheaf (p3StandardOpen K)
    (cubicPushforwardTwist K p hp m) n h

/-- Degree-two Hom cocycles for the ambient section-representer resolution. -/
abbrev CubicPushforwardAbstractDegreeTwoCocycle
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) :=
  DegreeTwoCocycle ((p3SectionRepresenterCechChain K).d 3 2)
    (Y := cubicPushforwardTwist K p hp m)

/-- Abstract Hom cocycles and raw ambient-pushforward Cech cocycles are
additively equivalent. -/
noncomputable def cubicPushforwardAbstractCocycleEquivRaw
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) :
    CubicPushforwardAbstractDegreeTwoCocycle K p hp m ≃+
      CubicPushforwardRawDegreeTwoCocycle K p hp m where
  toFun f := by
    refine ⟨cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 2 f.1, ?_⟩
    have hf := f.2
    change (p3SectionRepresenterCechChain K).d 3 2 ≫ f.1 = 0 at hf
    change (cubicPushforwardNegativeTwistCechComplex K p hp m).d 2 3
      (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 2 f.1) = 0
    rw [← cubicPushforwardSectionRepresenterCechHomEquiv_d, hf,
      cubicPushforwardSectionRepresenterCechHomEquiv_zero]
  invFun w := by
    let h := (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 2).symm w.1
    refine ⟨h, ?_⟩
    change (p3SectionRepresenterCechChain K).d 3 2 ≫ h = 0
    apply (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 3).injective
    rw [cubicPushforwardSectionRepresenterCechHomEquiv_d,
      Equiv.apply_symm_apply, w.2,
      cubicPushforwardSectionRepresenterCechHomEquiv_zero]
  left_inv f := by
    apply Subtype.ext
    exact (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 2).symm_apply_apply f.1
  right_inv w := by
    apply Subtype.ext
    exact (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 2).apply_symm_apply w.1
  map_add' f g := by
    apply Subtype.ext
    exact cubicPushforwardSectionRepresenterCechHomEquiv_add K p hp m 2 f.1 g.1

/-- The canonical degree-two comparison from abstract ambient Cech Hom
cocycles to Ext from the augmentation target. -/
def cubicPushforwardAbstractDegreeTwoToAugmentedExt
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    CubicPushforwardAbstractDegreeTwoCocycle K p hp m →
      Ext.{u} (p3SectionRepresenterCechTarget K)
        (cubicPushforwardTwist K p hp m) 2 := fun f => by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  exact augmentedChainDegreeTwoToExt
    (p3SectionRepresenterCechTarget K)
    ((p3SectionRepresenterCechChain K).X 0)
    ((p3SectionRepresenterCechChain K).X 1)
    ((p3SectionRepresenterCechChain K).X 2)
    ((p3SectionRepresenterCechChain K).X 3)
    (cubicPushforwardTwist K p hp m)
    (p3SectionRepresenterCechAugmentation K)
    ((p3SectionRepresenterCechChain K).d 1 0)
    ((p3SectionRepresenterCechChain K).d 2 1)
    ((p3SectionRepresenterCechChain K).d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) => p3StandardOpen K i.down)
      (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
    ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3SectionRepresenterCech_exact_two K) f

@[simp]
lemma cubicPushforwardAbstractDegreeTwoToAugmentedExt_zero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m 0 = 0 := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  unfold cubicPushforwardAbstractDegreeTwoToAugmentedExt
  exact augmentedChainDegreeTwoToExt_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma cubicPushforwardAbstractDegreeTwoToAugmentedExt_add
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (f g : CubicPushforwardAbstractDegreeTwoCocycle K p hp m) :
    cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m (f + g) =
      cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m f +
        cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m g := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  unfold cubicPushforwardAbstractDegreeTwoToAugmentedExt
  exact augmentedChainDegreeTwoToExt_add _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g

/-- The abstract ambient comparison as an additive homomorphism. -/
def cubicPushforwardAbstractDegreeTwoToAugmentedExtHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    CubicPushforwardAbstractDegreeTwoCocycle K p hp m →+
      Ext.{u} (p3SectionRepresenterCechTarget K)
        (cubicPushforwardTwist K p hp m) 2 where
  toFun := cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m
  map_zero' := cubicPushforwardAbstractDegreeTwoToAugmentedExt_zero K p hp m
  map_add' := cubicPushforwardAbstractDegreeTwoToAugmentedExt_add K p hp m

/-- Local acyclicity makes the abstract ambient degree-two comparison
surjective. -/
theorem cubicPushforwardAbstractDegreeTwoToAugmentedExt_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Function.Surjective
      (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m) := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  let h₀ := cubicPushforward_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    K p hp hp0 m 0
  let h₁ := cubicPushforward_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    K p hp hp0 m 1
  letI : Subsingleton (Ext.{u} ((p3SectionRepresenterCechChain K).X 0)
      (cubicPushforwardTwist K p hp m) 2) := h₀.2
  letI : Subsingleton (Ext.{u} ((p3SectionRepresenterCechChain K).X 1)
      (cubicPushforwardTwist K p hp m) 1) := h₁.1
  exact augmentedChainDegreeTwoToExt_surjective _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The abstract ambient comparison vanishes exactly on degree-one Hom
boundaries. -/
theorem cubicPushforwardAbstractDegreeTwoToAugmentedExt_eq_zero_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (f : CubicPushforwardAbstractDegreeTwoCocycle K p hp m) :
    cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m f = 0 ↔
      ∃ q : (p3SectionRepresenterCechChain K).X 1 ⟶
          cubicPushforwardTwist K p hp m,
        (p3SectionRepresenterCechChain K).d 2 1 ≫ q = f.1 := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  let h₀ := cubicPushforward_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    K p hp hp0 m 0
  letI : Subsingleton (Ext.{u} ((p3SectionRepresenterCechChain K).X 0)
      (cubicPushforwardTwist K p hp m) 1) := h₀.1
  exact augmentedChainDegreeTwoToExt_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f

/-- The raw ambient-pushforward degree-two comparison with ambient Ext. -/
noncomputable def cubicPushforwardRawDegreeTwoToAmbientExtHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    CubicPushforwardRawDegreeTwoCocycle K p hp m →+
      Ext.{u} (p3SectionRepresenterCechTarget K)
        (cubicPushforwardTwist K p hp m) 2 :=
  (cubicPushforwardAbstractDegreeTwoToAugmentedExtHom K p hp m).comp
    (cubicPushforwardAbstractCocycleEquivRaw K p hp m).symm.toAddMonoidHom

theorem cubicPushforwardRawDegreeTwoToAmbientExt_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Function.Surjective (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m) := by
  intro z
  obtain ⟨f, hf⟩ :=
    cubicPushforwardAbstractDegreeTwoToAugmentedExt_surjective K p hp hp0 m z
  refine ⟨cubicPushforwardAbstractCocycleEquivRaw K p hp m f, ?_⟩
  change cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m
    ((cubicPushforwardAbstractCocycleEquivRaw K p hp m).symm
      (cubicPushforwardAbstractCocycleEquivRaw K p hp m f)) = z
  rw [AddEquiv.symm_apply_apply]
  exact hf

/-- A raw ambient cocycle dies in ambient Ext exactly when it is a raw
degree-one Cech boundary. -/
theorem cubicPushforwardRawDegreeTwoToAmbientExt_eq_zero_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp m) :
    cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m w = 0 ↔
      ∃ y : (cubicPushforwardNegativeTwistCechComplex K p hp m).X 1,
        (cubicPushforwardNegativeTwistCechComplex K p hp m).d 1 2 y = w.1 := by
  let f := (cubicPushforwardAbstractCocycleEquivRaw K p hp m).symm w
  have hc := cubicPushforwardAbstractDegreeTwoToAugmentedExt_eq_zero_iff
    K p hp hp0 m f
  constructor
  · intro hw
    obtain ⟨q, hq⟩ := hc.mp hw
    refine ⟨cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 1 q, ?_⟩
    rw [← cubicPushforwardSectionRepresenterCechHomEquiv_d, hq]
    exact (cubicPushforwardAbstractCocycleEquivRaw K p hp m).apply_symm_apply w ▸ rfl
  · rintro ⟨y, hy⟩
    apply hc.mpr
    let q := (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 1).symm y
    refine ⟨q, ?_⟩
    apply (cubicPushforwardSectionRepresenterCechHomEquiv K p hp m 2).injective
    rw [cubicPushforwardSectionRepresenterCechHomEquiv_d,
      Equiv.apply_symm_apply, hy]
    exact (congrArg Subtype.val
      ((cubicPushforwardAbstractCocycleEquivRaw K p hp m).apply_symm_apply w)).symm

/-- The raw ambient degree-two Cech quotient computes ambient cohomology of
the pushed-forward cubic twist. -/
noncomputable def cubicPushforwardRawDegreeTwoQuotientEquivAmbientCohomologyTwo
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    CubicPushforwardRawDegreeTwoCocycle K p hp m ⧸
        (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m).ker ≃+
      schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp m) 2 :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m)
    (cubicPushforwardRawDegreeTwoToAmbientExt_surjective K p hp hp0 m)).trans
      (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K))

/-- The intrinsic and ambient raw comparison maps have the same kernel:
both kernels are exactly the raw degree-one Cech boundaries. -/
theorem cubicPushforwardRaw_intrinsicKer_eq_ambientKer
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (m : ℕ) :
    (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m).ker =
      (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m).ker := by
  ext w
  simp only [AddMonoidHom.mem_ker]
  rw [cubicPushforwardRawDegreeTwoToAugmentedExt_eq_zero_iff,
    cubicPushforwardRawDegreeTwoToAmbientExt_eq_zero_iff K p hp hp0 m]

/-- Cohomology of an intrinsic cubic twist agrees with cohomology of its
ambient pushforward, constructed through their common raw Cech quotient. -/
noncomputable def cubicIntrinsicCohomologyTwoEquivPushforward
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (m : ℕ) :
    schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
        (sheafOfModules (grading (equationIdeal p hp)) m) 2 ≃+
      schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp m) 2 :=
  (cubicPushforwardRawDegreeTwoQuotientEquivCohomologyTwo K p hp m).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq
      (cubicPushforwardRaw_intrinsicKer_eq_ambientKer K p hp hp0 m)).trans
        (cubicPushforwardRawDegreeTwoQuotientEquivAmbientCohomologyTwo
          K p hp hp0 m))

/-- The fully internal cubic-surface degree-two duality needed in Voisin's
argument: intrinsic `H²(O_S(-3))` is the dual of ambient quadrics. -/
noncomputable def cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] :
    schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
        (sheafOfModules (grading (equationIdeal p hp)) 3) 2 ≃+
      Module.Dual K (homogeneousSubmodule (Fin 4) K 2) :=
  (cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 3).trans
    (cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic
      K p hp hp0)

end PfaffianDescent.ProjectiveNegativeTwist
