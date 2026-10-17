import PfaffianDescent.SerreExtensionPencilGluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Recovering actual closed kernels from their affine open pullbacks -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_kernel_eq_of_affine_pullbacks
    {X Z T : Scheme.{u}} (i : Z ⟶ X) (j : T ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ k, (U k).1 = ⊤)
    (h : ∀ k, (pullback.snd i (U k).1.ι).ker =
      (pullback.snd j (U k).1.ι).ker) : i.ker = j.ker := by
  let A (k : ι) : X.affineOpens :=
    ⟨(U k).1.ι ''ᵁ (⊤ : (U k).1.toScheme.Opens),
      (isAffineOpen_top (U k).1.toScheme).image_of_isOpenImmersion (U k).1.ι⟩
  have hA : ⨆ k, (A k).1 = ⊤ := by
    simpa only [A, Scheme.Opens.ι_image_top] using hU
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top A hA
  intro k
  let V := (U k).1.toScheme
  let W : V.affineOpens := ⟨⊤, isAffineOpen_top V⟩
  have hi := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i
    (pullback.snd i (U k).1.ι) (pullback.fst i (U k).1.ι) (U k).1.ι
    (IsPullback.of_hasPullback i (U k).1.ι).flip W
  have hj := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j
    (pullback.snd j (U k).1.ι) (pullback.fst j (U k).1.ι) (U k).1.ι
    (IsPullback.of_hasPullback j (U k).1.ι).flip W
  have he := congrArg (fun I : V.IdealSheafData => I.ideal W) (h k)
  rw [hi, hj] at he
  exact (Ideal.comap_injective_of_surjective ((U k).1.ι.appIso W).inv.hom
    (ConcreteCategory.bijective_of_isIso ((U k).1.ι.appIso W).inv).2) he

end PfaffianDescent
