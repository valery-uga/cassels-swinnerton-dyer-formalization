import PfaffianDescent.TripleLineProductAtlas

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

def tripleLineCoordinateEquiv : TripleLineCoordinate ≃ Fin 3 where
  toFun := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  invFun := ![Sum.inl (0, 0), Sum.inr (Sum.inl (0, 0)), Sum.inr (Sum.inr (0, 0))]
  left_inv := by
    rintro (⟨a, b⟩ | (⟨a, b⟩ | ⟨a, b⟩)) <;> fin_cases a <;> fin_cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

section
variable (K : Type u) [CommRing K]

noncomputable def lineTripleCoordinateIso : Spec (.of (MvPolynomial (Fin 3) K)) ≅
    Spec (.of (MvPolynomial TripleLineCoordinate K)) :=
  Scheme.Spec.mapIso (MvPolynomial.renameEquiv K tripleLineCoordinateEquiv).toRingEquiv.toCommRingCatIso.op

lemma lineTripleCoordinateIso_zero :
    (lineTripleCoordinateIso K).hom ≫ polynomialSumFirst K LineCoordinate PairLineCoordinate =
      grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X 0)) := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) tripleLineCoordinateEquiv).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inl : LineCoordinate → TripleLineCoordinate)).toRingHom) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (fun _ : LineCoordinate => MvPolynomial.X (0 : Fin 3))).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.rename tripleLineCoordinateEquiv (MvPolynomial.rename Sum.inl (MvPolynomial.C a)) = _
    simp
  · intro j
    change MvPolynomial.rename tripleLineCoordinateEquiv (MvPolynomial.rename Sum.inl (MvPolynomial.X j)) = _
    simp [tripleLineCoordinateEquiv]

lemma lineTripleCoordinateIso_one :
    (lineTripleCoordinateIso K).hom ≫
      (polynomialSumSecond K LineCoordinate PairLineCoordinate ≫ polynomialSumFirst K LineCoordinate LineCoordinate) =
        grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X 1)) := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) tripleLineCoordinateEquiv).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inr : PairLineCoordinate → TripleLineCoordinate)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inl : LineCoordinate → PairLineCoordinate)).toRingHom)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (fun _ : LineCoordinate => MvPolynomial.X (1 : Fin 3))).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.rename tripleLineCoordinateEquiv (MvPolynomial.rename Sum.inr (MvPolynomial.rename Sum.inl (MvPolynomial.C a))) = _
    simp
  · intro j
    change MvPolynomial.rename tripleLineCoordinateEquiv (MvPolynomial.rename Sum.inr (MvPolynomial.rename Sum.inl (MvPolynomial.X j))) = _
    simp [tripleLineCoordinateEquiv]

lemma lineTripleCoordinateIso_two :
    (lineTripleCoordinateIso K).hom ≫
      (polynomialSumSecond K LineCoordinate PairLineCoordinate ≫ polynomialSumSecond K LineCoordinate LineCoordinate) =
        grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X 2)) := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) tripleLineCoordinateEquiv).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inr : PairLineCoordinate → TripleLineCoordinate)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inr : LineCoordinate → PairLineCoordinate)).toRingHom)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (fun _ : LineCoordinate => MvPolynomial.X (2 : Fin 3))).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.rename tripleLineCoordinateEquiv (MvPolynomial.rename Sum.inr (MvPolynomial.rename Sum.inr (MvPolynomial.C a))) = _
    simp
  · intro j
    change MvPolynomial.rename tripleLineCoordinateEquiv (MvPolynomial.rename Sum.inr (MvPolynomial.rename Sum.inr (MvPolynomial.X j))) = _
    simp [tripleLineCoordinateEquiv]

lemma lineTripleCoordinateIso_chart (ε : Fin 3 → Bool) :
    (lineTripleCoordinateIso K).hom ≫ lineTripleProductChartMap K (ε 0) (ε 1) (ε 2) = lineTripleChartMap K ε := by
  apply lineTriple_hom_ext K
  intro i
  apply Eq.trans _ (lineTripleChartMap_projection K ε i).symm
  fin_cases i
  · change ((lineTripleCoordinateIso K).hom ≫ lineTripleProductChartMap K (ε 0) (ε 1) (ε 2)) ≫
      lineTripleProjection K 0 =
        grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X 0)) ≫ lineChartMap K (ε 0)
    rw [Category.assoc, lineTripleProductChartMap_zero, ← Category.assoc, lineTripleCoordinateIso_zero]
    rfl
  · change ((lineTripleCoordinateIso K).hom ≫ lineTripleProductChartMap K (ε 0) (ε 1) (ε 2)) ≫
      lineTripleProjection K 1 =
        grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X 1)) ≫ lineChartMap K (ε 1)
    rw [Category.assoc, lineTripleProductChartMap_one, ← Category.assoc, ← Category.assoc]
    rw [Category.assoc (lineTripleCoordinateIso K).hom, lineTripleCoordinateIso_one]
    rfl
  · change ((lineTripleCoordinateIso K).hom ≫ lineTripleProductChartMap K (ε 0) (ε 1) (ε 2)) ≫
      lineTripleProjection K 2 =
        grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X 2)) ≫ lineChartMap K (ε 2)
    rw [Category.assoc, lineTripleProductChartMap_two, ← Category.assoc, ← Category.assoc]
    rw [Category.assoc (lineTripleCoordinateIso K).hom, lineTripleCoordinateIso_two]
    rfl

instance lineTripleChartMap_open (ε : Fin 3 → Bool) : IsOpenImmersion (lineTripleChartMap K ε) := by
  rw [← lineTripleCoordinateIso_chart]
  exact inferInstanceAs (IsOpenImmersion ((lineTripleCoordinateIso K).hom ≫
    lineTripleProductChartMap K (ε 0) (ε 1) (ε 2)))

lemma lineTripleCharts_cover (x : lineTripleScheme K) :
    ∃ ε : Fin 3 → Bool, ∃ y : goodMixedPairScheme K, lineTripleChartMap K ε y = x := by
  obtain ⟨a, b, c, y, hy⟩ := lineTripleProductCharts_cover K x
  refine ⟨![a, b, c], (lineTripleCoordinateIso K).inv y, ?_⟩
  rw [← lineTripleCoordinateIso_chart]
  have he : (lineTripleCoordinateIso K).hom ((lineTripleCoordinateIso K).inv y) = y := by
    change ((lineTripleCoordinateIso K).inv ≫ (lineTripleCoordinateIso K).hom) y = y
    rw [Iso.inv_hom_id]
    rfl
  change lineTripleProductChartMap K a b c
    ((lineTripleCoordinateIso K).hom ((lineTripleCoordinateIso K).inv y)) = x
  rw [he]
  exact hy

/-- The product has the same eight affine coordinate domains as the pair-isotropic fiber. -/
noncomputable def lineTripleOpenCover : Scheme.OpenCover.{u} (lineTripleScheme K) where
  I₀ := ULift.{u} (Fin 3 → Bool)
  X _ := goodMixedPairScheme K
  f ε := lineTripleChartMap K ε.down
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨ε, y, hy⟩ := lineTripleCharts_cover K x
      exact ⟨⟨ε⟩, y, hy⟩
    · intro ε
      exact lineTripleChartMap_open K ε.down

end
end PfaffianDescent
