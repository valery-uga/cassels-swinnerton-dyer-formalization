import AllCharacteristics.ProjectiveChartOverlap
import AllCharacteristics.GradedTripleChartMaps

/-!
# Actual triple intersections of projective coefficient charts

The product of three coordinates gives the actual intersection of a two-chart
intersection with the third chart. All three pair intersections restrict to
that same spectrum, and their maps agree on the shared coordinate charts.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- The actual product-coordinate overlap as an open subscheme of the projective scheme. -/
noncomputable def chartOverlapι (i j : σ) : Spec (.of (ChartOverlapRing I i j)) ⟶ scheme I :=
  Proj.awayι (grading I) (coordinate I i * coordinate I j)
    (SetLike.mul_mem_graded (coordinate_mem I i) (coordinate_mem I j)) (by decide : 0 < 2)

/-- The pair-overlap product chart is an open subscheme. -/
instance isOpenImmersion_chartOverlapι (i j : σ) : IsOpenImmersion (chartOverlapι I i j) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (grading I) (coordinate I i * coordinate I j)
    (SetLike.mul_mem_graded (coordinate_mem I i) (coordinate_mem I j)) (by decide : 0 < 2)))

/-- The first overlap restriction followed by its chart embedding is the overlap embedding. -/
theorem chartOverlapLeftMap_toProj (i j : σ) :
    Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I i j)) ≫ chartι I i = chartOverlapι I i j :=
  Proj.SpecMap_awayMap_awayι (grading I) (coordinate_mem I i) (by decide : 0 < 1)
    (coordinate_mem I j) rfl

/-- The second overlap restriction has the same embedding into the projective scheme. -/
theorem chartOverlapRightMap_toProj (i j : σ) :
    Spec.map (CommRingCat.ofHom (chartOverlapRightMap I i j)) ≫ chartι I j = chartOverlapι I i j :=
  Proj.SpecMap_awayMap_awayι (grading I) (coordinate_mem I j) (by decide : 0 < 1)
    (coordinate_mem I i) (mul_comm _ _)

/-- The homogeneous ring of the actual three-chart intersection. -/
abbrev ChartTripleRing (i j l : σ) :=
  Away (grading I) (coordinate I i * coordinate I j * coordinate I l)

/-- The triple-product chart embeds into the projective scheme. -/
noncomputable def chartTripleι (i j l : σ) : Spec (.of (ChartTripleRing I i j l)) ⟶ scheme I :=
  Proj.awayι (grading I) (coordinate I i * coordinate I j * coordinate I l)
    (SetLike.mul_mem_graded (SetLike.mul_mem_graded (coordinate_mem I i) (coordinate_mem I j))
      (coordinate_mem I l)) (by decide : 0 < 3)

/-- The triple-product chart is an open subscheme. -/
instance isOpenImmersion_chartTripleι (i j l : σ) : IsOpenImmersion (chartTripleι I i j l) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (grading I) (coordinate I i * coordinate I j * coordinate I l)
    (SetLike.mul_mem_graded (SetLike.mul_mem_graded (coordinate_mem I i) (coordinate_mem I j))
      (coordinate_mem I l)) (by decide : 0 < 3)))

/-- Restriction from the first two charts' intersection to the triple intersection. -/
noncomputable def chartTripleFromFirstPair (i j l : σ) :
    ChartOverlapRing I i j →+* ChartTripleRing I i j l :=
  awayMap (grading I) (coordinate_mem I l) rfl

/-- Restriction from the last two charts' intersection to the same triple intersection. -/
noncomputable def chartTripleFromLastPair (i j l : σ) :
    ChartOverlapRing I j l →+* ChartTripleRing I i j l :=
  awayMap (grading I) (coordinate_mem I i) ((mul_assoc _ _ _).trans (mul_comm _ _))

/-- Restriction from the outer two charts' intersection to the same triple intersection. -/
noncomputable def chartTripleFromOuterPair (i j l : σ) :
    ChartOverlapRing I i l →+* ChartTripleRing I i j l :=
  awayMap (grading I) (coordinate_mem I j) (mul_right_comm _ _ _)

/-- Restriction from the first pair commutes with the embedding into the projective scheme. -/
theorem chartTripleFromFirstPair_toProj (i j l : σ) :
    Spec.map (CommRingCat.ofHom (chartTripleFromFirstPair I i j l)) ≫ chartOverlapι I i j =
      chartTripleι I i j l :=
  Proj.SpecMap_awayMap_awayι (grading I)
    (SetLike.mul_mem_graded (coordinate_mem I i) (coordinate_mem I j)) (by decide : 0 < 2)
    (coordinate_mem I l) rfl

/-- Restriction from the last pair gives the same triple embedding. -/
theorem chartTripleFromLastPair_toProj (i j l : σ) :
    Spec.map (CommRingCat.ofHom (chartTripleFromLastPair I i j l)) ≫ chartOverlapι I j l =
      chartTripleι I i j l :=
  GradedChart.lastPair_toProj (grading I) (coordinate_mem I i) (coordinate_mem I j) (coordinate_mem I l)

/-- Restriction from the outer pair gives the same triple embedding. -/
theorem chartTripleFromOuterPair_toProj (i j l : σ) :
    Spec.map (CommRingCat.ofHom (chartTripleFromOuterPair I i j l)) ≫ chartOverlapι I i l =
      chartTripleι I i j l :=
  GradedChart.outerPair_toProj (grading I) (coordinate_mem I i) (coordinate_mem I j) (coordinate_mem I l)

/-- The triple ring is the spectrum of the actual intersection of the first
pair overlap with the third coordinate chart. -/
noncomputable def chartTripleOverlapIso (i j l : σ) :
    pullback (chartOverlapι I i j) (chartι I l) ≅ Spec (.of (ChartTripleRing I i j l)) :=
  Proj.pullbackAwayιIso (grading I)
    (SetLike.mul_mem_graded (coordinate_mem I i) (coordinate_mem I j)) (by decide : 0 < 2)
    (coordinate_mem I l) (by decide : 0 < 1) rfl

/-- The actual triple-intersection identification has the specified first-pair projection. -/
theorem chartTripleOverlapIso_inv_fst (i j l : σ) :
    (chartTripleOverlapIso I i j l).inv ≫ pullback.fst (chartOverlapι I i j) (chartι I l) =
      Spec.map (CommRingCat.ofHom (chartTripleFromFirstPair I i j l)) :=
  Proj.pullbackAwayιIso_inv_fst (grading I)
    (SetLike.mul_mem_graded (coordinate_mem I i) (coordinate_mem I j)) (by decide : 0 < 2)
    (coordinate_mem I l) (by decide : 0 < 1) rfl

/-- Spectrum sends composition of coefficient ring homomorphisms to reverse composition. -/
theorem specMap_ringHom_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

/-- A map into an affine coordinate chart is determined by its projective composite. -/
theorem chartRingMap_eq_of_toProj {A : Type u} [CommRing A] (i : σ)
    (f g : ChartRing I i →+* A)
    (h : Spec.map (CommRingCat.ofHom f) ≫ chartι I i =
      Spec.map (CommRingCat.ofHom g) ≫ chartι I i) : f = g := by
  have he := Spec.map_injective ((cancel_mono (chartι I i)).mp h)
  exact congrArg (fun k : CommRingCat.of (ChartRing I i) ⟶ CommRingCat.of A ↦ k.hom) he

/-- The first and last pair restrictions agree on their shared middle chart. -/
theorem chartTriple_middle_compat (i j l : σ) :
    (chartTripleFromFirstPair I i j l).comp (chartOverlapRightMap I i j) =
      (chartTripleFromLastPair I i j l).comp (chartOverlapLeftMap I j l) := by
  apply chartRingMap_eq_of_toProj I j
  rw [specMap_ringHom_comp, specMap_ringHom_comp, Category.assoc, Category.assoc,
    chartOverlapRightMap_toProj, chartOverlapLeftMap_toProj,
    chartTripleFromFirstPair_toProj, chartTripleFromLastPair_toProj]

/-- The first and outer pair restrictions agree on their shared first chart. -/
theorem chartTriple_first_compat (i j l : σ) :
    (chartTripleFromFirstPair I i j l).comp (chartOverlapLeftMap I i j) =
      (chartTripleFromOuterPair I i j l).comp (chartOverlapLeftMap I i l) := by
  apply chartRingMap_eq_of_toProj I i
  rw [specMap_ringHom_comp, specMap_ringHom_comp, Category.assoc, Category.assoc,
    chartOverlapLeftMap_toProj, chartOverlapLeftMap_toProj,
    chartTripleFromFirstPair_toProj, chartTripleFromOuterPair_toProj]

/-- The last and outer pair restrictions agree on their shared last chart. -/
theorem chartTriple_last_compat (i j l : σ) :
    (chartTripleFromLastPair I i j l).comp (chartOverlapRightMap I j l) =
      (chartTripleFromOuterPair I i j l).comp (chartOverlapRightMap I i l) := by
  apply chartRingMap_eq_of_toProj I l
  rw [specMap_ringHom_comp, specMap_ringHom_comp, Category.assoc, Category.assoc,
    chartOverlapRightMap_toProj, chartOverlapRightMap_toProj,
    chartTripleFromLastPair_toProj, chartTripleFromOuterPair_toProj]

/-- The triple-intersection identification has the actual last-chart restriction as its second projection. -/
theorem chartTripleOverlapIso_inv_snd (i j l : σ) :
    (chartTripleOverlapIso I i j l).inv ≫ pullback.snd (chartOverlapι I i j) (chartι I l) =
      Spec.map (CommRingCat.ofHom
        ((chartTripleFromLastPair I i j l).comp (chartOverlapRightMap I j l))) := by
  apply (cancel_mono (chartι I l)).mp
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, chartTripleOverlapIso_inv_fst,
    chartTripleFromFirstPair_toProj, specMap_ringHom_comp, Category.assoc,
    chartOverlapRightMap_toProj, chartTripleFromLastPair_toProj]

/-- The displayed triple restrictions form the actual Cartesian intersection square. -/
theorem isPullback_chartTripleOverlap (i j l : σ) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartTripleFromFirstPair I i j l)))
      (Spec.map (CommRingCat.ofHom
        ((chartTripleFromLastPair I i j l).comp (chartOverlapRightMap I j l))))
      (chartOverlapι I i j) (chartι I l) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (chartTripleOverlapIso I i j l).symm
    (chartTripleOverlapIso_inv_fst I i j l) (chartTripleOverlapIso_inv_snd I i j l)
  rw [chartTripleFromFirstPair_toProj, specMap_ringHom_comp, Category.assoc,
    chartOverlapRightMap_toProj, chartTripleFromLastPair_toProj]

end HomogeneousProjective
end AllCharacteristics
