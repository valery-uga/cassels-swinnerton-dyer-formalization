import PfaffianDescent.OriginalNormalizedProjectiveReduction312

/-! SOURCE ONLY317. Physical normalized original chart reductions for specified
coefficient-changed equations and their actual composition. The compatibility
needed for197/classifier naturality is DERIVED by the original projective
coefficient map, then cancelled through its original open chart. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private lemma normalizedTowerConjugate_factor317 {C : Type*} [Category C]
    {U X V Y : C} (e : U ≅ X) (f : X ⟶ Y) (a : V ≅ Y) :
    ((e.hom ≫ f) ≫ a.inv) ≫ a.hom = e.hom ≫ f := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma normalizedTowerConjugate_isPullback317
    {U X V Y B0 B : Scheme.{u}} (e : U ≅ X) (a : V ≅ Y)
    (f : X ⟶ Y) (F0 : X ⟶ B0) (F : Y ⟶ B) (b : B0 ⟶ B)
    (G0 : U ⟶ B0) (G : V ⟶ B)
    (h0 : e.hom ≫ F0 = G0) (h : a.hom ≫ F = G)
    (H : IsPullback f F0 F b) :
    IsPullback ((e.hom ≫ f) ≫ a.inv) G0 G b := by
  apply H.of_iso' e a (Iso.refl _) (Iso.refl _)
  · exact (normalizedTowerConjugate_factor317 e f a).symm
  · exact h0.trans (Category.comp_id _).symm
  · exact h.trans (Category.comp_id _).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

private lemma normalizedTowerConjugate_embedding317 {C : Type*} [Category C]
    {U X V Y Z W : C} (e : U ≅ X) (a : V ≅ Y) (f : X ⟶ Y)
    (i : Y ⟶ Z) (i0 : X ⟶ W) (d : W ⟶ Z) (h : i0 ≫ d = f ≫ i) :
    ((e.hom ≫ f) ≫ a.inv) ≫ (a.hom ≫ i) = (e.hom ≫ i0) ≫ d :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ i) (normalizedTowerConjugate_factor317 e f a)).trans
      ((Category.assoc e.hom f i).trans
        ((congrArg (fun t => e.hom ≫ t) h.symm).trans (Category.assoc e.hom i0 d).symm)))

variable {R S : Type u} [CommRing R] [CommRing S]
variable (b : R →+* S) (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
variable (s : MvPolynomial (Fin 4) S) (hs : s.IsHomogeneous d) (he : r.map b = s) (j : Fin 4)

/-- General exact physical equation change, preserving the specified original
polynomials instead of coercing independently synthesized algebra towers. -/
def originalNormalizedProjectiveReductionOfEquation317 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 s j)) ⟶
      Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)) :=
  ((originalNormalizedHypersurfaceChartSpecIso312 s hs j).hom ≫
    Spec.map (CommRingCat.ofHom
      (chartCoefficientMap b (equationIdeal r hr) (equationIdeal s hs)
        (equationIdeal_map_of_eq b r hr s hs he) j))) ≫
    (originalNormalizedHypersurfaceChartSpecIso312 r hr j).inv

lemma originalNormalizedProjectiveReductionOfEquation_isPullback317 :
    IsPullback (originalNormalizedProjectiveReductionOfEquation317 b r hr s hs he j)
      (Spec.map (CommRingCat.ofHom (R := S) (S := OriginalNormalizedHypersurfaceAlgebra312 s j)
        (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 s j))))
      (Spec.map (CommRingCat.ofHom (R := R) (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
        (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 r j))))
      (Spec.map (CommRingCat.ofHom b)) :=
  normalizedTowerConjugate_isPullback317
    (originalNormalizedHypersurfaceChartSpecIso312 s hs j)
    (originalNormalizedHypersurfaceChartSpecIso312 r hr j) _ _ _ _ _ _
    (originalNormalizedHypersurfaceChartSpecIso_toBase312 s hs j)
    (originalNormalizedHypersurfaceChartSpecIso_toBase312 r hr j)
    (isPullback_chartCoefficientMap b (equationIdeal r hr) (equationIdeal s hs)
      (equationIdeal_map_of_eq b r hr s hs he) j)

lemma originalNormalizedProjectiveReductionOfEquation_toOriginal317 :
    originalNormalizedProjectiveReductionOfEquation317 b r hr s hs he j ≫
        originalNormalizedHypersurfaceChartEmbedding312 r hr j =
      originalNormalizedHypersurfaceChartEmbedding312 s hs j ≫
        hypersurfaceReductionMap b r hr s hs he := by
  have hchart : chartι (equationIdeal s hs) j ≫ hypersurfaceReductionMap b r hr s hs he =
      Spec.map (CommRingCat.ofHom
        (chartCoefficientMap b (equationIdeal r hr) (equationIdeal s hs)
          (equationIdeal_map_of_eq b r hr s hs he) j)) ≫ chartι (equationIdeal r hr) j :=
    (congrArg (fun t => chartι (equationIdeal s hs) j ≫ t)
      (hypersurfaceReductionMap_eq_projectiveCoefficientMap b r hr s hs he)).trans
        (chartι_projectiveCoefficientMap b (equationIdeal r hr) (equationIdeal s hs)
          (equationIdeal_map_of_eq b r hr s hs he) j)
  exact normalizedTowerConjugate_embedding317
    (originalNormalizedHypersurfaceChartSpecIso312 s hs j)
    (originalNormalizedHypersurfaceChartSpecIso312 r hr j) _
    (chartι (equationIdeal r hr) j) (chartι (equationIdeal s hs) j)
    (hypersurfaceReductionMap b r hr s hs he) hchart

lemma originalNormalizedProjectiveReductionOfEquation_default317 :
    originalNormalizedProjectiveReductionOfEquation317 b r hr (r.map b) (hr.map b) rfl j =
      originalNormalizedProjectiveChartReduction312 b r hr j := rfl

include he in
private lemma nativeNormalizedTowerCompositeEquation317
    {T : Type u} [CommRing T] (c : S →+* T)
    (t : MvPolynomial (Fin 4) T) (hct : s.map c = t) : r.map (c.comp b) = t :=
  (MvPolynomial.map_map b c r).symm.trans ((congrArg (MvPolynomial.map c) he).trans hct)

private lemma nativeNormalizedOriginalProjective_comp317
    {T : Type u} [CommRing T] (c : S →+* T)
    (t : MvPolynomial (Fin 4) T) (ht : t.IsHomogeneous d) (hct : s.map c = t) :
    hypersurfaceReductionMap c s hs t ht hct ≫ hypersurfaceReductionMap b r hr s hs he =
      hypersurfaceReductionMap (c.comp b) r hr t ht
        (nativeNormalizedTowerCompositeEquation317 b r s he c t hct) := by
  rw [hypersurfaceReductionMap_eq_projectiveCoefficientMap,
    hypersurfaceReductionMap_eq_projectiveCoefficientMap,
    hypersurfaceReductionMap_eq_projectiveCoefficientMap]
  exact projectiveCoefficientMap_comp b c (equationIdeal r hr) (equationIdeal s hs)
    (equationIdeal t ht) (equationIdeal_map_of_eq b r hr s hs he)
    (equationIdeal_map_of_eq c s hs t ht hct)

local instance originalNormalizedTowerChartOpen317
    {A : Type u} [CommRing A] (p : MvPolynomial (Fin 4) A)
    {e : ℕ} (hp : p.IsHomogeneous e) (k : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 p hp k) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 p hp k

/-- Actual physical compatibility for the future197/classifier diagram.
It follows from original projective composition, cancelled through ORIGINAL
open embedding. No classifier compatibility or desired lift is an intake. -/
lemma originalNormalizedProjectiveReductionOfEquation_comp317
    {T : Type u} [CommRing T] (c : S →+* T)
    (t : MvPolynomial (Fin 4) T) (ht : t.IsHomogeneous d) (hct : s.map c = t) :
    originalNormalizedProjectiveReductionOfEquation317 c s hs t ht hct j ≫
        originalNormalizedProjectiveReductionOfEquation317 b r hr s hs he j =
      originalNormalizedProjectiveReductionOfEquation317 (c.comp b) r hr t ht
        (nativeNormalizedTowerCompositeEquation317 b r s he c t hct) j := by
  apply (cancel_mono (originalNormalizedHypersurfaceChartEmbedding312 r hr j)).mp
  calc
    _ = originalNormalizedProjectiveReductionOfEquation317 c s hs t ht hct j ≫
        (originalNormalizedProjectiveReductionOfEquation317 b r hr s hs he j ≫
          originalNormalizedHypersurfaceChartEmbedding312 r hr j) := Category.assoc _ _ _
    _ = originalNormalizedProjectiveReductionOfEquation317 c s hs t ht hct j ≫
        (originalNormalizedHypersurfaceChartEmbedding312 s hs j ≫
          hypersurfaceReductionMap b r hr s hs he) :=
      congrArg (fun u => originalNormalizedProjectiveReductionOfEquation317 c s hs t ht hct j ≫ u)
        (originalNormalizedProjectiveReductionOfEquation_toOriginal317 b r hr s hs he j)
    _ = (originalNormalizedProjectiveReductionOfEquation317 c s hs t ht hct j ≫
        originalNormalizedHypersurfaceChartEmbedding312 s hs j) ≫
          hypersurfaceReductionMap b r hr s hs he := (Category.assoc _ _ _).symm
    _ = (originalNormalizedHypersurfaceChartEmbedding312 t ht j ≫
        hypersurfaceReductionMap c s hs t ht hct) ≫ hypersurfaceReductionMap b r hr s hs he :=
      congrArg (fun u => u ≫ hypersurfaceReductionMap b r hr s hs he)
        (originalNormalizedProjectiveReductionOfEquation_toOriginal317 c s hs t ht hct j)
    _ = originalNormalizedHypersurfaceChartEmbedding312 t ht j ≫
        (hypersurfaceReductionMap c s hs t ht hct ≫ hypersurfaceReductionMap b r hr s hs he) :=
      Category.assoc _ _ _
    _ = originalNormalizedHypersurfaceChartEmbedding312 t ht j ≫
        hypersurfaceReductionMap (c.comp b) r hr t ht
          (nativeNormalizedTowerCompositeEquation317 b r s he c t hct) :=
      congrArg (fun u => originalNormalizedHypersurfaceChartEmbedding312 t ht j ≫ u)
        (nativeNormalizedOriginalProjective_comp317 b r hr s hs he c t ht hct)
    _ = _ := (originalNormalizedProjectiveReductionOfEquation_toOriginal317
      (c.comp b) r hr t ht (nativeNormalizedTowerCompositeEquation317 b r s he c t hct) j).symm

end PfaffianDescent
end
