import PfaffianDescent.AffineQCAcyclicity
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Genuine native affine QC-kernel closure from exact tilde, not a
supplied QC-kernel or cohomology certificate. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma conjugatedPreimage_comm
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Full]
    {A B : C} {M N : D} (eA : F.obj A ≅ M) (eB : F.obj B ≅ N) (f : M ⟶ N) :
    F.map (F.preimage (eA.hom ≫ f ≫ eB.inv)) ≫ eB.hom = eA.hom ≫ f := by
  rw [F.map_preimage]
  simp only [Category.assoc, eB.inv_hom_id, Category.comp_id]

/-- Kernels of maps between ACTUAL QC modules on Spec R are QC for the
native sheaf-module action. The comparison is constructed by exact tilde
and its actual full native Hom map; no desired kernel iso is assumed. -/
theorem affineNative_kernel_isQuasicoherent
    (R : CommRingCat.{u}) {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let F := tilde.functor R
  letI : PreservesFiniteLimits F := PfaffianDescent.tilde_preservesFiniteLimits (R := R)
  have hM : F.essImage M := by
    rw [AlgebraicGeometry.essImage_tilde]
    exact (inferInstance : M.IsQuasicoherent)
  have hN : F.essImage N := by
    rw [AlgebraicGeometry.essImage_tilde]
    exact (inferInstance : N.IsQuasicoherent)
  obtain ⟨A, ⟨eA⟩⟩ := hM
  obtain ⟨B, ⟨eB⟩⟩ := hN
  let φ := F.preimage (eA.hom ≫ f ≫ eB.inv)
  have hcomm : F.map φ ≫ eB.hom = eA.hom ≫ f :=
    conjugatedPreimage_comm F eA eB f
  let e : F.obj (kernel φ) ≅ kernel f :=
    PreservesKernel.iso F φ ≪≫ kernel.mapIso (F.map φ) f eA eB hcomm
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (show (F.obj (kernel φ)).IsQuasicoherent from inferInstance)

end PfaffianDescent.Coray
