import PfaffianDescent.PolynomialProjectiveMap
import PfaffianDescent.CoordinateMatchingLineGradedPair
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! SOURCE ONLY, UNVERIFIED. GENUINE projective-scheme isomorphism to P1,
with actual structure-morphism compatibility over E. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable (E : Type u) [Field E]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "J" => coordinateMatchingLineIdeal (K := E) false
local notation "PS₂" => homogeneousSubmodule (Fin 2) E

def coordinateMatchingLineP1Iso : scheme J ≅ Proj PS₂ := by
  change Proj (grading J) ≅ Proj PS₂
  let F := coordinateMatchingLineGradedRestriction E
  let G := coordinateMatchingLineGradedInclusion E
  let hF := gradedSurjective_irrelevant_le F
    (coordinateMatchingLineGradedRestriction_surjective E)
  let hG := gradedSurjective_irrelevant_le G
    (coordinateMatchingLineGradedInclusion_surjective E)
  refine { hom := Proj.map G hG
           inv := Proj.map F hF
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · rw [← Proj.map_comp F G hF hG]
    have h : G.comp F = GradedRingHom.id (grading J) :=
      coordinateMatchingLineGradedInclusion_comp_restriction E
    simpa only [h] using (Proj.map_id (𝒜 := grading J))
  · rw [← Proj.map_comp G F hG hF]
    have h : F.comp G = GradedRingHom.id PS₂ :=
      coordinateMatchingLineGradedRestriction_comp_inclusion E
    simpa only [h] using (Proj.map_id (𝒜 := PS₂))

theorem coordinateMatchingLineGradedInclusion_away_base (s : MvPolynomial (Fin 2) E) :
    (Away.map (coordinateMatchingLineGradedInclusion E) s).comp
      (AllCharacteristics.GradedChart.baseMap PS₂ (z := s)) =
      AllCharacteristics.GradedChart.baseMap (grading J)
        (z := coordinateMatchingLineGradedInclusion E s) := by
  apply RingHom.ext
  intro a
  apply val_injective
  change Localization.mk
      (coordinateMatchingLineGradedInclusion E (algebraMap E (MvPolynomial (Fin 2) E) a))
      ⟨coordinateMatchingLineGradedInclusion E 1, _⟩ =
    Localization.mk (algebraMap E (CoordinateRing J) a) 1
  have hbase : coordinateMatchingLineGradedInclusion E
      (algebraMap E (MvPolynomial (Fin 2) E) a) =
      algebraMap E (CoordinateRing J) a := by
    change Ideal.Quotient.mk (J).toIdeal (MvPolynomial.rename
      (Fin.castAdd 2 : Fin 2 → Fin 4) (C a)) = Ideal.Quotient.mk (J).toIdeal (C a)
    rw [MvPolynomial.rename_C]
  rw [hbase]
  exact congrArg (Localization.mk (algebraMap E (CoordinateRing J) a))
    (Subtype.ext (map_one (coordinateMatchingLineGradedInclusion E)))

@[reassoc] theorem coordinateMatchingLineP1Iso_hom_toBase :
    (coordinateMatchingLineP1Iso E).hom ≫
      ambientToBase (R := E) (σ := Fin 2) = toBase J := by
  let G := coordinateMatchingLineGradedInclusion E
  let hG := gradedSurjective_irrelevant_le G
    (coordinateMatchingLineGradedInclusion_surjective E)
  change Proj.map G hG ≫ ambientToBase (R := E) (σ := Fin 2) = toBase J
  apply (Proj.mapAffineOpenCover G hG).openCover.hom_ext
  intro s
  change (Σ d : PNat, PS₂ d) at s
  obtain ⟨⟨d, hd⟩, s, hs⟩ := s
  change s ∈ PS₂ d at hs
  have hb : Proj.awayι PS₂ s hs hd ≫ ambientToBase (R := E) (σ := Fin 2) =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap PS₂ (z := s))) := by
    change Proj.awayι PS₂ s hs hd ≫
      (Proj.toSpecZero PS₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap E (PS₂ 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have hbJ : Proj.awayι (grading J) (G s) (G.2 hs) hd ≫ toBase J =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading J) (z := G s))) :=
    homogeneousChart_toBase J (G s) (G.2 hs) hd
  change Proj.awayι (grading J) (G s) (G.2 hs) hd ≫
    (Proj.map G hG ≫ ambientToBase (R := E) (σ := Fin 2)) =
      Proj.awayι (grading J) (G s) (G.2 hs) hd ≫ toBase J
  rw [← Category.assoc, Proj.awayι_comp_map G hG hd s hs, Category.assoc,
    hb, hbJ, ← Spec.map_comp]
  apply congrArg Spec.map
  rw [← CommRingCat.ofHom_comp]
  exact congrArg CommRingCat.ofHom
    (coordinateMatchingLineGradedInclusion_away_base E s)

end PfaffianDescent.QuarticNet
