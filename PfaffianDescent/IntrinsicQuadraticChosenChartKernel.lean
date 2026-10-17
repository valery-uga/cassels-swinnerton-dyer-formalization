import PfaffianDescent.IntrinsicFullQuadraticSystem

/-! Actual intrinsic ideal-sheaf vanishing on a chosen standard chart implies
vanishing in that chart's actual coordinate algebra. This is independent of
reducedness and preserves nilpotents. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The standard chart's actual affine reconstruction commutes with its
canonical homogeneous-localization section map. -/
theorem ambientCoordinateChart_fromSpec (j : Fin 4) :
    Spec.map (Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j)) ≫
      Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
        (isHomogeneous_X k j) (by decide : 0 < 1) =
      (intrinsicQuadraticAmbientOpen (K := k) j).2.fromSpec := by
  let U := Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X j)
  let hU : IsAffineOpen U := (intrinsicQuadraticAmbientOpen (K := k) j).2
  letI : IsAffine U := hU
  letI : IsIso U.toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  apply (cancel_epi U.toSpecΓ).mp
  calc
    U.toSpecΓ ≫ (Spec.map (Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j)) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
          (isHomogeneous_X k j) (by decide : 0 < 1)) =
      Proj.basicOpenToSpec (homogeneousSubmodule (Fin 4) k) (X j) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
          (isHomogeneous_X k j) (by decide : 0 < 1) := by
      rw [← Category.assoc]
      rfl
    _ = U.ι := by
      change (Proj.basicOpenIsoSpec (homogeneousSubmodule (Fin 4) k) (X j)
        (isHomogeneous_X k j) (by decide : 0 < 1)).hom ≫
        ((Proj.basicOpenIsoSpec (homogeneousSubmodule (Fin 4) k) (X j)
          (isHomogeneous_X k j) (by decide : 0 < 1)).inv ≫ U.ι) = U.ι
      simp
    _ = U.toSpecΓ ≫ hU.fromSpec := hU.toSpecΓ_fromSpec.symm

variable {A : Type u} [CommRing A]

def ambientCoordinateChartSpecPoint (j : Fin 4)
    (h : Away (homogeneousSubmodule (Fin 4) k) (X j) →+* A) :
    Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) k) :=
  Spec.map (CommRingCat.ofHom h) ≫
    Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
      (isHomogeneous_X k j) (by decide : 0 < 1)

theorem ambientCoordinateChartSpecPoint_whole (j : Fin 4)
    (h : Away (homogeneousSubmodule (Fin 4) k) (X j) →+* A) :
    ⊤ ≤ (ambientCoordinateChartSpecPoint j h) ⁻¹ᵁ
      (intrinsicQuadraticAmbientOpen (K := k) j).1 := by
  letI : IsOpenImmersion (Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
      (isHomogeneous_X k j) (by decide : 0 < 1)) := by
    unfold Proj.awayι
    infer_instance
  intro x _
  change Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
      (isHomogeneous_X k j) (by decide : 0 < 1)
      (Spec.map (CommRingCat.ofHom h) x) ∈
    Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X j)
  rw [← Proj.opensRange_awayι (homogeneousSubmodule (Fin 4) k) (X j)
    (isHomogeneous_X k j) (by decide : 0 < 1)]
  exact Scheme.Hom.mem_opensRange.mpr ⟨Spec.map (CommRingCat.ofHom h) x, rfl⟩

/-- Pulling actual sections to the whole affine source recovers exactly its
specified chart ring map, proved via affine reconstruction naturality. -/
theorem ambientCoordinateChartSpecPoint_appLE (j : Fin 4)
    (h : Away (homogeneousSubmodule (Fin 4) k) (X j) →+* A) :
    Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j) ≫
      (ambientCoordinateChartSpecPoint j h).appLE
        (intrinsicQuadraticAmbientOpen (K := k) j).1 ⊤
        (ambientCoordinateChartSpecPoint_whole j h) ≫
      (Scheme.ΓSpecIso (.of A)).hom = CommRingCat.ofHom h := by
  let f := ambientCoordinateChartSpecPoint j h
  let U := intrinsicQuadraticAmbientOpen (K := k) j
  let t := Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
    (isHomogeneous_X k j) (by decide : 0 < 1)
  letI : IsOpenImmersion t := by
    dsimp only [t, Proj.awayι]
    infer_instance
  apply Spec.map_injective
  apply (cancel_mono t).mp
  calc
    Spec.map (Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j) ≫
        f.appLE U.1 ⊤ (ambientCoordinateChartSpecPoint_whole j h) ≫
        (Scheme.ΓSpecIso (.of A)).hom) ≫ t =
      Spec.map (Scheme.ΓSpecIso (.of A)).hom ≫
        Spec.map (f.appLE U.1 ⊤ (ambientCoordinateChartSpecPoint_whole j h)) ≫
        (Spec.map (Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j)) ≫ t) := by
      simp only [Spec.map_comp, Category.assoc]
    _ = Spec.map (Scheme.ΓSpecIso (.of A)).hom ≫
        Spec.map (f.appLE U.1 ⊤ (ambientCoordinateChartSpecPoint_whole j h)) ≫
        U.2.fromSpec := by rw [ambientCoordinateChart_fromSpec]
    _ = Spec.map (Scheme.ΓSpecIso (.of A)).hom ≫ (Spec (.of A)).isoSpec.inv ≫ f := by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec f U.2 (isAffineOpen_top _)
        (ambientCoordinateChartSpecPoint_whole j h), IsAffineOpen.fromSpec_top]
    _ = f := by
      rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc]
      simp
    _ = Spec.map (CommRingCat.ofHom h) ≫ t := rfl

/-- A member of the ACTUAL ideal-sheaf kernel vanishes in the actual chart
algebra; no assumed sheaf-to-coordinate comparison is used. -/
theorem intrinsicQuadraticChartIdeal_specPoint_evaluation_zero
    (j : Fin 4) (h : Away (homogeneousSubmodule (Fin 4) k) (X j) →+* A)
    [QuasiCompact (ambientCoordinateChartSpecPoint j h)]
    (q : MvPolynomial (Fin 4) k)
    (hq : q ∈ intrinsicQuadraticChartIdeal (ambientCoordinateChartSpecPoint j h) j) :
    h (ambientChartEvaluation j q) = 0 := by
  let f := ambientCoordinateChartSpecPoint j h
  let U := intrinsicQuadraticAmbientOpen (K := k) j
  let a := ambientChartEvaluation j q
  let ev := Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j)
  have hm : ev a ∈ f.ker.ideal U := hq
  have hz : f.app U.1 (ev a) = 0 := by
    rw [f.ker_apply U] at hm
    change f.app U.1 (ev a) = 0 at hm
    exact hm
  have hLE : f.appLE U.1 ⊤ (ambientCoordinateChartSpecPoint_whole j h) (ev a) = 0 := by
    change (Spec (.of A)).presheaf.map _ (f.app U.1 (ev a)) = 0
    rw [hz, map_zero]
  have he := congrArg (fun g => g a) (ambientCoordinateChartSpecPoint_appLE j h)
  change (Scheme.ΓSpecIso (.of A)).hom
      (f.appLE U.1 ⊤ (ambientCoordinateChartSpecPoint_whole j h) (ev a)) = h a at he
  rw [hLE, map_zero] at he
  exact he.symm

end PfaffianDescent
