import PfaffianDescent.VoisinCubicPushforwardCechTerms
import PfaffianDescent.VoisinCubicQuotientRawCechExt

/-!
# Raw Cech cocycles for the ambient pushforward of a cubic twist

The complex isomorphism between the ambient-pushforward and intrinsic Cech
complexes restricts to an additive equivalence on degree-two cocycles.
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

/-- Raw degree-two Cech cocycles of the ambient pushforward of the intrinsic
cubic twist. -/
abbrev CubicPushforwardRawDegreeTwoCocycle
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) :=
  AddMonoidHom.ker
    ((cubicPushforwardNegativeTwistCechComplex K p hp m).d 2 3).hom

/-- The degree-two component map sends ambient-pushforward cocycles to
intrinsic cubic cocycles. -/
def cubicPushforwardRawCocycleToQuotient
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp m) :
    CubicQuotientRawDegreeTwoCocycle K (equationIdeal p hp) m := by
  refine ⟨(cubicPushforwardCechTermIso K p hp m 2).hom w.1, ?_⟩
  have h := ConcreteCategory.congr_hom
    (cubicPushforwardCechTermIso_d_succ K p hp m 2) w.1
  simp only [ConcreteCategory.comp_apply] at h
  change (quotientNegativeTwistCechComplex (equationIdeal p hp) m).d 2 3
    ((cubicPushforwardCechTermIso K p hp m 2).hom w.1) = 0
  rw [h, w.2, map_zero]

/-- The inverse degree-two component map sends intrinsic cubic cocycles back
to ambient-pushforward cocycles. -/
def cubicQuotientRawCocycleToPushforward
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ)
    (w : CubicQuotientRawDegreeTwoCocycle K (equationIdeal p hp) m) :
    CubicPushforwardRawDegreeTwoCocycle K p hp m := by
  refine ⟨(cubicPushforwardCechTermIso K p hp m 2).inv w.1, ?_⟩
  have h := ConcreteCategory.congr_hom
    (cubicPushforwardCechTermIso_d_succ K p hp m 2)
    ((cubicPushforwardCechTermIso K p hp m 2).inv w.1)
  simp only [ConcreteCategory.comp_apply] at h
  have hz :
      (cubicPushforwardCechTermIso K p hp m 3).hom
        ((cubicPushforwardNegativeTwistCechComplex K p hp m).d 2 3
          ((cubicPushforwardCechTermIso K p hp m 2).inv w.1)) = 0 := by
    rw [← h, Iso.inv_hom_id_apply, w.2]
  apply (ProjectiveNegativeTwist.addCommGrpIsoAddEquiv
    (cubicPushforwardCechTermIso K p hp m 3)).injective
  change (cubicPushforwardCechTermIso K p hp m 3).hom
      ((cubicPushforwardNegativeTwistCechComplex K p hp m).d 2 3
        ((cubicPushforwardCechTermIso K p hp m 2).inv w.1)) =
    (cubicPushforwardCechTermIso K p hp m 3).hom 0
  rw [hz, map_zero]

/-- Ambient-pushforward and intrinsic raw degree-two Cech cocycles are
additively equivalent. -/
noncomputable def cubicPushforwardDegreeTwoCocycleEquivQuotient
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) :
    CubicPushforwardRawDegreeTwoCocycle K p hp m ≃+
      CubicQuotientRawDegreeTwoCocycle K (equationIdeal p hp) m where
  toFun := cubicPushforwardRawCocycleToQuotient K p hp m
  invFun := cubicQuotientRawCocycleToPushforward K p hp m
  left_inv w := by
    apply Subtype.ext
    exact Iso.hom_inv_id_apply
      (cubicPushforwardCechTermIso K p hp m 2) w.1
  right_inv w := by
    apply Subtype.ext
    exact Iso.inv_hom_id_apply
      (cubicPushforwardCechTermIso K p hp m 2) w.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (ProjectiveNegativeTwist.addCommGrpIsoAddEquiv
      (cubicPushforwardCechTermIso K p hp m 2)) x.1 y.1

/-- The ambient-pushforward raw Cech cocycle comparison with the intrinsic
augmented `Ext²` group. -/
noncomputable def cubicPushforwardRawDegreeTwoToAugmentedExtHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] (m : ℕ) :
    CubicPushforwardRawDegreeTwoCocycle K p hp m →+
      Ext.{u} (quotientSectionRepresenterCechTarget (equationIdeal p hp))
        (sheafOfModules (grading (equationIdeal p hp)) m) 2 :=
  (cubicQuotientRawDegreeTwoToAugmentedExtHom K (equationIdeal p hp) m).comp
    (cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m).toAddMonoidHom

/-- Every intrinsic augmented `Ext²` class is represented by an
ambient-pushforward raw Cech cocycle. -/
theorem cubicPushforwardRawDegreeTwoToAugmentedExt_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] (m : ℕ) :
    Function.Surjective
      (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m) := by
  intro z
  obtain ⟨w, hw⟩ :=
    cubicQuotientRawDegreeTwoToAugmentedExt_surjective K
      (equationIdeal p hp) m z
  refine ⟨(cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m).symm w, ?_⟩
  change cubicQuotientRawDegreeTwoToAugmentedExtHom K (equationIdeal p hp) m
    (cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m
      ((cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m).symm w)) = z
  rw [AddEquiv.apply_symm_apply]
  exact hw

/-- The intrinsic comparison, expressed on ambient-pushforward raw
cocycles, vanishes exactly on ambient raw degree-one boundaries. -/
theorem cubicPushforwardRawDegreeTwoToAugmentedExt_eq_zero_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] (m : ℕ)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp m) :
    cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m w = 0 ↔
      ∃ y : (cubicPushforwardNegativeTwistCechComplex K p hp m).X 1,
        (cubicPushforwardNegativeTwistCechComplex K p hp m).d 1 2 y = w.1 := by
  let e := cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m
  have hc := cubicQuotientRawDegreeTwoToAugmentedExt_eq_zero_iff K
    (equationIdeal p hp) m (e w)
  constructor
  · intro hw
    have hw' : cubicQuotientRawDegreeTwoToAugmentedExtHom K
        (equationIdeal p hp) m (e w) = 0 := hw
    obtain ⟨y, hy⟩ := hc.mp hw'
    let x := (cubicPushforwardCechTermIso K p hp m 1).inv y
    refine ⟨x, ?_⟩
    have hd := ConcreteCategory.congr_hom
      (cubicPushforwardCechTermIso_d_succ K p hp m 1) x
    simp only [ConcreteCategory.comp_apply] at hd
    apply (ProjectiveNegativeTwist.addCommGrpIsoAddEquiv
      (cubicPushforwardCechTermIso K p hp m 2)).injective
    change (cubicPushforwardCechTermIso K p hp m 2).hom
        ((cubicPushforwardNegativeTwistCechComplex K p hp m).d 1 2 x) =
      (cubicPushforwardCechTermIso K p hp m 2).hom w.1
    rw [← hd]
    have hxy : (cubicPushforwardCechTermIso K p hp m 1).hom x = y := by
      dsimp only [x]
      exact Iso.inv_hom_id_apply _ y
    rw [hxy, hy]
    rfl
  · rintro ⟨x, hx⟩
    have hw' : cubicQuotientRawDegreeTwoToAugmentedExtHom K
        (equationIdeal p hp) m (e w) = 0 := by
      apply hc.mpr
      refine ⟨(cubicPushforwardCechTermIso K p hp m 1).hom x, ?_⟩
      have hd := ConcreteCategory.congr_hom
        (cubicPushforwardCechTermIso_d_succ K p hp m 1) x
      simp only [ConcreteCategory.comp_apply] at hd
      rw [hd, hx]
      rfl
    exact hw'

/-- The quotient of ambient-pushforward raw degree-two cocycles by the
comparison kernel computes intrinsic second cohomology of the cubic. -/
noncomputable def cubicPushforwardRawDegreeTwoQuotientEquivCohomologyTwo
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] (m : ℕ) :
    CubicPushforwardRawDegreeTwoCocycle K p hp m ⧸
        (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m).ker ≃+
      schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
        (sheafOfModules (grading (equationIdeal p hp)) m) 2 :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m)
    (cubicPushforwardRawDegreeTwoToAugmentedExt_surjective K p hp m)).trans
      (extPrecompIsoOfIso
        (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)))

end PfaffianDescent.ProjectiveNegativeTwist
