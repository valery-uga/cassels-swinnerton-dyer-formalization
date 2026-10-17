import PfaffianDescent.CorayActualPositiveThreeTermIdealHOne

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Genuine eventual H1 vanishing for the ORIGINAL whole ideal tensored
with the ORIGINAL ambient positive coefficient, over any field. Every
polynomial generator, syzygy, homogeneous weight and native sequence is
derived internally; no global lifting or Serre-vanishing premise is added. -/
theorem homogeneousIdeal_eventually_actualIdealTwist_cohomology_one_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (I : HomogeneousIdeal PS) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (schemeModuleCohomology (Proj PS)
        (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
          (positiveSheafOfModules PS m)) 1) := by
  classical
  obtain ⟨T, d, R, e, S, f, B, hI, hd, hR, he, hS, hf⟩ :=
    homogeneousIdeal_exists_actual_finite_homogeneousThreeTermPresentation I
  have hTset : Set.range (fun i : T => i.val) = (T : Set PolyA) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact i.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hRset : Set.range (fun a : R => a.val) = (R : Set (T → PolyA)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact a.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hSset : Set.range (fun l : S => l.val) = (S : Set (R → PolyA)) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩; exact l.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hspanG : Ideal.span (Set.range (fun i : T => i.val)) = I.toIdeal := by
    rw [hTset]; exact hI
  have hspanR : Submodule.span PolyA (Set.range (fun a : R => a.val)) =
      (actualPolynomialGeneratorMap (fun i : T => i.val)).ker := by
    rw [hRset]; exact hR
  have hspanS : Submodule.span PolyA (Set.range (fun l : S => l.val)) =
      (actualPolynomialRelationMap (fun a : R => a.val)).ker := by
    rw [hSset]; exact hS
  refine ⟨B, fun m hm => ?_⟩
  exact actualPositiveThreeTermPresentation_idealTwist_hOne_subsingleton I
    (fun i : T => i.val) d (fun i => (hd i).2)
    (fun a : R => a.val) e (fun a => (he a).2)
    (fun l : S => l.val) f (fun l => (hf l).2)
    hspanG hspanR hspanS m
    (fun i => (hd i).1.trans hm) (fun a => (he a).1.trans hm)
    (fun l => (hf l).1.trans hm)

end PfaffianDescent.Coray
