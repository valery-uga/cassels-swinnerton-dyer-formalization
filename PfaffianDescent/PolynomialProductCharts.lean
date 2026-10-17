import PfaffianDescent.PolynomialSchemeProduct

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v w
section
variable (K : Type u) [CommRing K] (ι σ : Type)

noncomputable abbrev polynomialSchemeBase : Spec (.of (MvPolynomial ι K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K)))

noncomputable abbrev polynomialSumFirst : Spec (.of (MvPolynomial (ι ⊕ σ) K)) ⟶ Spec (.of (MvPolynomial ι K)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inl : ι → ι ⊕ σ)).toRingHom)

noncomputable abbrev polynomialSumSecond : Spec (.of (MvPolynomial (ι ⊕ σ) K)) ⟶ Spec (.of (MvPolynomial σ K)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inr : σ → ι ⊕ σ)).toRingHom)

lemma polynomialSumFirst_toBase :
    polynomialSumFirst K ι σ ≫ polynomialSchemeBase K ι = polynomialSchemeBase K (ι ⊕ σ) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.rename (R := K) (Sum.inl : ι → ι ⊕ σ)).comp_algebraMap

lemma polynomialSumSecond_toBase :
    polynomialSumSecond K ι σ ≫ polynomialSchemeBase K σ = polynomialSchemeBase K (ι ⊕ σ) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.rename (R := K) (Sum.inr : σ → ι ⊕ σ)).comp_algebraMap

variable {X Y : Scheme.{u}} (bX : X ⟶ Spec (.of K)) (bY : Y ⟶ Spec (.of K))
  (f : Spec (.of (MvPolynomial ι K)) ⟶ X) (g : Spec (.of (MvPolynomial σ K)) ⟶ Y)
  (hf : f ≫ bX = polynomialSchemeBase K ι) (hg : g ≫ bY = polynomialSchemeBase K σ)

include hf hg in
lemma polynomialProductChart_isPullback :
    IsPullback (polynomialSumFirst K ι σ) (polynomialSumSecond K ι σ) (f ≫ bX) (g ≫ bY) := by
  rw [hf, hg]
  exact polynomialSum_isPullback K ι σ

noncomputable def polynomialProductChartIso : Spec (.of (MvPolynomial (ι ⊕ σ) K)) ≅
    pullback (f ≫ bX) (g ≫ bY) :=
  (polynomialProductChart_isPullback K ι σ bX bY f g hf hg).isoPullback

/-- The product of two affine coordinate charts, with the combined polynomial coordinate ring. -/
noncomputable def polynomialProductChartMap : Spec (.of (MvPolynomial (ι ⊕ σ) K)) ⟶ pullback bX bY :=
  (polynomialProductChartIso K ι σ bX bY f g hf hg).hom ≫
    pullback.map (f ≫ bX) (g ≫ bY) bX bY f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)

lemma polynomialProductChartMap_fst :
    polynomialProductChartMap K ι σ bX bY f g hf hg ≫ pullback.fst bX bY =
      polynomialSumFirst K ι σ ≫ f := by
  unfold polynomialProductChartMap polynomialProductChartIso pullback.map
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst]

lemma polynomialProductChartMap_snd :
    polynomialProductChartMap K ι σ bX bY f g hf hg ≫ pullback.snd bX bY =
      polynomialSumSecond K ι σ ≫ g := by
  unfold polynomialProductChartMap polynomialProductChartIso pullback.map
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, IsPullback.isoPullback_hom_snd]

lemma polynomialProductChartMap_toBase :
    polynomialProductChartMap K ι σ bX bY f g hf hg ≫ (pullback.fst bX bY ≫ bX) =
      polynomialSchemeBase K (ι ⊕ σ) := by
  rw [← Category.assoc, polynomialProductChartMap_fst, Category.assoc, hf]
  exact polynomialSumFirst_toBase K ι σ

instance polynomialProductChartMap_open [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (polynomialProductChartMap K ι σ bX bY f g hf hg) := by
  unfold polynomialProductChartMap
  infer_instance

end
section
variable (K : Type u) [CommRing K] (ι σ : Type)
  {X Y : Scheme.{u}} (bX : X ⟶ Spec (.of K)) (bY : Y ⟶ Spec (.of K))
  {I : Type v} {J : Type w}
  (f : I → (Spec (.of (MvPolynomial ι K)) ⟶ X))
  (g : J → (Spec (.of (MvPolynomial σ K)) ⟶ Y))
  (hf : ∀ i, f i ≫ bX = polynomialSchemeBase K ι)
  (hg : ∀ j, g j ≫ bY = polynomialSchemeBase K σ)
  [∀ i, IsOpenImmersion (f i)] [∀ j, IsOpenImmersion (g j)]

lemma polynomialProductCharts_cover
    (hfc : ∀ x : X, ∃ i y, f i y = x) (hgc : ∀ y : Y, ∃ j z, g j z = y)
    (x : (pullback bX bY : Scheme)) :
    ∃ i j y, polynomialProductChartMap K ι σ bX bY (f i) (g j) (hf i) (hg j) y = x := by
  let U : Scheme.OpenCover.{v} X := {
    I₀ := I, X := fun _ => Spec (.of (MvPolynomial ι K)), f := f
    mem₀ := (Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨hfc, fun _ => inferInstance⟩ }
  let V : Scheme.OpenCover.{w} Y := {
    I₀ := J, X := fun _ => Spec (.of (MvPolynomial σ K)), f := g
    mem₀ := (Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨hgc, fun _ => inferInstance⟩ }
  obtain ⟨⟨i, j⟩, y, hy⟩ := (Scheme.Pullback.openCoverOfLeftRight U V bX bY).exists_eq x
  let e := polynomialProductChartIso K ι σ bX bY (f i) (g j) (hf i) (hg j)
  refine ⟨i, j, e.inv y, ?_⟩
  change (e.hom ≫ pullback.map (f i ≫ bX) (g j ≫ bY) bX bY (f i) (g j) (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)) (e.inv y) = x
  have he : e.hom (e.inv y) = y := by
    change (e.inv ≫ e.hom) y = y
    rw [e.inv_hom_id]
    rfl
  rw [Scheme.Hom.comp_apply, he]
  exact hy

end
end PfaffianDescent
