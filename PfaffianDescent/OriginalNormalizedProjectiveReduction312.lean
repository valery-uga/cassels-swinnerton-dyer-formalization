import PfaffianDescent.OriginalNormalizedHypersurfaceAffineChart312
import AllCharacteristics.HypersurfaceCoefficientNaturality
import PfaffianDescent.FiniteFlatHilbertTestPoints195

/-! SOURCE ONLY312. The constructed normalized original polynomial chart
commutes with the ORIGINAL projective hypersurface reduction. Whole ideal
reduction therefore remains exact in that SAME affine chart. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private lemma normalizedProjectiveChartSpecScalar312
    {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    (c : R →+* C) (e : C →+* A) (a : R →+* A) (h : e.comp c = a) :
    Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom c) =
      Spec.map (CommRingCat.ofHom a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

lemma originalNormalizedHypersurfaceChartSpecIso_toBase312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) :
    (originalNormalizedHypersurfaceChartSpecIso312 p hp j).hom ≫
        Spec.map (CommRingCat.ofHom (chartBaseMap (equationIdeal p hp) j)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))) := by
  have h : (originalNormalizedHypersurfaceChartAlgEquiv312 p hp j).toRingHom.comp
      (chartBaseMap (equationIdeal p hp) j) =
        algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j) :=
    RingHom.ext (originalNormalizedHypersurfaceChartAlgEquiv_base312 p hp j)
  exact normalizedProjectiveChartSpecScalar312
    (chartBaseMap (equationIdeal p hp) j)
    (originalNormalizedHypersurfaceChartAlgEquiv312 p hp j).toRingHom
    (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j)) h

private lemma normalizedChartConjugate_factor312
    {C : Type*} [Category C] {U X V Y : C}
    (e : U ≅ X) (f : X ⟶ Y) (a : V ≅ Y) :
    ((e.hom ≫ f) ≫ a.inv) ≫ a.hom = e.hom ≫ f := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma normalizedChartConjugate_isPullback312
    {U X V Y B0 B : Scheme.{u}} (e : U ≅ X) (a : V ≅ Y)
    (f : X ⟶ Y) (F0 : X ⟶ B0) (F : Y ⟶ B) (b : B0 ⟶ B)
    (G0 : U ⟶ B0) (G : V ⟶ B)
    (h0 : e.hom ≫ F0 = G0) (h : a.hom ≫ F = G)
    (H : IsPullback f F0 F b) :
    IsPullback ((e.hom ≫ f) ≫ a.inv) G0 G b := by
  apply H.of_iso' e a (Iso.refl _) (Iso.refl _)
  · exact (normalizedChartConjugate_factor312 e f a).symm
  · exact h0.trans (Category.comp_id _).symm
  · exact h.trans (Category.comp_id _).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

variable {R S : Type u} [CommRing R] [CommRing S]
variable (b : R →+* S) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
variable (j : Fin 4)

/-- The physical original projective chart coefficient map, transported by
the internally constructed normalized original chart isomorphisms. -/
def originalNormalizedProjectiveChartReduction312 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j)) ⟶
      Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 p j)) :=
  ((originalNormalizedHypersurfaceChartSpecIso312 (p.map b) (hp.map b) j).hom ≫
    Spec.map (CommRingCat.ofHom
      (chartCoefficientMap b (equationIdeal p hp) (equationIdeal (p.map b) (hp.map b))
        (equationIdeal_map b p hp) j))) ≫
    (originalNormalizedHypersurfaceChartSpecIso312 p hp j).inv

/-- This physical original projective reduction is Cartesian over the actual
normalized polynomial scalar maps, without a supplied chart square. -/
lemma originalNormalizedProjectiveChartReduction_isPullback312 :
    IsPullback (originalNormalizedProjectiveChartReduction312 b p hp j)
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))))
      (Spec.map (CommRingCat.ofHom b)) :=
  normalizedChartConjugate_isPullback312
    (originalNormalizedHypersurfaceChartSpecIso312 (p.map b) (hp.map b) j)
    (originalNormalizedHypersurfaceChartSpecIso312 p hp j)
    (Spec.map (CommRingCat.ofHom
      (chartCoefficientMap b (equationIdeal p hp) (equationIdeal (p.map b) (hp.map b))
        (equationIdeal_map b p hp) j)))
    (Spec.map (CommRingCat.ofHom (chartBaseMap (equationIdeal (p.map b) (hp.map b)) j)))
    (Spec.map (CommRingCat.ofHom (chartBaseMap (equationIdeal p hp) j)))
    (Spec.map (CommRingCat.ofHom b))
    (Spec.map (CommRingCat.ofHom
      (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j))))
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))))
    (originalNormalizedHypersurfaceChartSpecIso_toBase312 (p.map b) (hp.map b) j)
    (originalNormalizedHypersurfaceChartSpecIso_toBase312 p hp j)
    (isPullback_chartCoefficientMap b (equationIdeal p hp)
      (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp) j)

lemma originalNormalizedProjectiveChartReduction_toBase312 :
    originalNormalizedProjectiveChartReduction312 b p hp j ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))) =
      Spec.map (CommRingCat.ofHom
          (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j))) ≫
        Spec.map (CommRingCat.ofHom b) :=
  (originalNormalizedProjectiveChartReduction_isPullback312 b p hp j).w

private lemma normalizedChartConjugate_embedding312
    {C : Type*} [Category C] {U X V Y Z W : C}
    (e : U ≅ X) (a : V ≅ Y) (f : X ⟶ Y)
    (i : Y ⟶ Z) (i0 : X ⟶ W) (d : W ⟶ Z) (h : i0 ≫ d = f ≫ i) :
    ((e.hom ≫ f) ≫ a.inv) ≫ (a.hom ≫ i) = (e.hom ≫ i0) ≫ d :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ i) (normalizedChartConjugate_factor312 e f a)).trans
      ((Category.assoc e.hom f i).trans
        ((congrArg (fun t => e.hom ≫ t) h.symm).trans (Category.assoc e.hom i0 d).symm)))

/-- Exact SAME original projective ambient maps, not only maps over the base. -/
lemma originalNormalizedProjectiveChartReduction_toOriginal312 :
    originalNormalizedProjectiveChartReduction312 b p hp j ≫
        originalNormalizedHypersurfaceChartEmbedding312 p hp j =
      originalNormalizedHypersurfaceChartEmbedding312 (p.map b) (hp.map b) j ≫
        hypersurfaceReductionMap b p hp (p.map b) (hp.map b) rfl := by
  have hchart : chartι (equationIdeal (p.map b) (hp.map b)) j ≫
      hypersurfaceReductionMap b p hp (p.map b) (hp.map b) rfl =
    Spec.map (CommRingCat.ofHom
      (chartCoefficientMap b (equationIdeal p hp) (equationIdeal (p.map b) (hp.map b))
        (equationIdeal_map b p hp) j)) ≫ chartι (equationIdeal p hp) j :=
    (congrArg (fun t => chartι (equationIdeal (p.map b) (hp.map b)) j ≫ t)
      (hypersurfaceReductionMap_eq_projectiveCoefficientMap b p hp (p.map b) (hp.map b) rfl)).trans
        (chartι_projectiveCoefficientMap b (equationIdeal p hp)
          (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp) j)
  exact normalizedChartConjugate_embedding312
    (originalNormalizedHypersurfaceChartSpecIso312 (p.map b) (hp.map b) j)
    (originalNormalizedHypersurfaceChartSpecIso312 p hp j) _
    (chartι (equationIdeal p hp) j) (chartι (equationIdeal (p.map b) (hp.map b)) j)
    (hypersurfaceReductionMap b p hp (p.map b) (hp.map b) rfl) hchart

/-- A whole original195 deformation equality remains exact on the specified
normalized affine chart. The hypothesis is precisely the physical whole-ideal
reduction supplied by195, not an outcome about a coefficient classifier. -/
lemma originalNormalizedProjectiveChartReduction_wholeIdeal312
    (I : (hypersurface p hp).IdealSheafData)
    (I0 : (hypersurface (p.map b) (hp.map b)).IdealSheafData)
    (h : I.comap (hypersurfaceReductionMap b p hp (p.map b) (hp.map b) rfl) = I0) :
    (I.comap (originalNormalizedHypersurfaceChartEmbedding312 p hp j)).comap
        (originalNormalizedProjectiveChartReduction312 b p hp j) =
      I0.comap (originalNormalizedHypersurfaceChartEmbedding312 (p.map b) (hp.map b) j) :=
  (I.comap_comp (originalNormalizedProjectiveChartReduction312 b p hp j)
    (originalNormalizedHypersurfaceChartEmbedding312 p hp j)).symm.trans
      ((congrArg I.comap (originalNormalizedProjectiveChartReduction_toOriginal312 b p hp j)).trans
        ((I.comap_comp (originalNormalizedHypersurfaceChartEmbedding312 (p.map b) (hp.map b) j)
          (hypersurfaceReductionMap b p hp (p.map b) (hp.map b) rfl)).trans
            (congrArg (fun J => J.comap
              (originalNormalizedHypersurfaceChartEmbedding312 (p.map b) (hp.map b) j)) h)))

end PfaffianDescent
end
