import PfaffianDescent.AffineQuotientPushforwardTilde
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! Actual affine cokernel sections, derived from the tilde–Gamma adjunction.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Cokernels of actual affine modules in the tilde essential image are
actually sheafifications of their global module cokernels. -/
def affineCokernelFromTildeGammaIso
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)]
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) N)] :
    (tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map f)) ≅ cokernel f := by
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  letI hm : IsIso ((tilde.adjunction (R := R)).counit.app M) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) M)
    infer_instance
  letI hn : IsIso ((tilde.adjunction (R := R)).counit.app N) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) N)
    infer_instance
  let eM : F.obj (G.obj M) ≅ M := asIso ((tilde.adjunction (R := R)).counit.app M)
  let eN : F.obj (G.obj N) ≅ N := asIso ((tilde.adjunction (R := R)).counit.app N)
  have hnat : F.map (G.map f) ≫ eN.hom = eM.hom ≫ f := by
    change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫
        (tilde.adjunction (R := R)).counit.app N =
      (tilde.adjunction (R := R)).counit.app M ≫ f
    exact (tilde.adjunction (R := R)).counit.naturality f
  exact PreservesCokernel.iso F (G.map f) ≪≫
    cokernel.mapIso (F.map (G.map f)) f eM eN hnat

/-- The constructed sheaf comparison preserves the actual cokernel projection. -/
theorem affineCokernelFromTildeGammaIso_π
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)]
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) N)] :
    (tilde.functor R).map (cokernel.π (moduleSpecΓFunctor.map f)) ≫
      (affineCokernelFromTildeGammaIso f).hom =
      Scheme.Modules.fromTildeΓ (R := R) N ≫ cokernel.π f := by
  dsimp only [affineCokernelFromTildeGammaIso, Iso.trans_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- Actual sections of the actual SHEAF cokernel agree with the actual
module cokernel of sections. This is constructed, not an assumption that
Gamma is right exact for arbitrary module sheaves. -/
def affineSheafCokernelSectionsIso
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)]
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) N)] :
    (moduleSpecΓFunctor (R := R)).obj (cokernel f) ≅
      cokernel (moduleSpecΓFunctor.map f) :=
  (moduleSpecΓFunctor (R := R)).mapIso (affineCokernelFromTildeGammaIso f).symm ≪≫
    (tilde.isoTop (cokernel (moduleSpecΓFunctor.map f))).symm

/-- The actual affine section comparison takes the actual sheaf quotient map
to the actual module quotient projection. -/
theorem affineSheafCokernelSectionsIso_π
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)]
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) N)] :
    (moduleSpecΓFunctor (R := R)).map (cokernel.π f) ≫
      (affineSheafCokernelSectionsIso f).hom =
      cokernel.π (moduleSpecΓFunctor.map f) := by
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  let g := G.map f
  let e := affineCokernelFromTildeGammaIso f
  let η := (tilde.adjunction (R := R)).unit
  apply (cancel_mono (affineSheafCokernelSectionsIso f).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change G.map (cokernel.π f) = cokernel.π g ≫ η.app (cokernel g) ≫ G.map e.hom
  have hnat : cokernel.π g ≫ η.app (cokernel g) =
      η.app (G.obj N) ≫ G.map (F.map (cokernel.π g)) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      η.naturality (cokernel.π g)
  have hprojection : F.map (cokernel.π g) ≫ e.hom =
      (tilde.adjunction (R := R)).counit.app N ≫ cokernel.π f := by
    exact affineCokernelFromTildeGammaIso_π f
  rw [← Category.assoc, hnat, Category.assoc, ← G.map_comp,
    hprojection, G.map_comp]
  rw [← Category.assoc]
  have htriangle : η.app (G.obj N) ≫
      G.map ((tilde.adjunction (R := R)).counit.app N) = 𝟙 (G.obj N) :=
    (tilde.adjunction (R := R)).right_triangle_components N
  rw [htriangle, Category.id_comp]

end PfaffianDescent.Coray
