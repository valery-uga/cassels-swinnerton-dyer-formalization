import PfaffianDescent.TripleLineScheme
import PfaffianDescent.PolynomialProductCharts

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

abbrev LineCoordinate := Fin 1 × Fin 1
abbrev PairLineCoordinate := LineCoordinate ⊕ LineCoordinate
abbrev TripleLineCoordinate := LineCoordinate ⊕ PairLineCoordinate

section
variable (K : Type u) [CommRing K]

/-- A standard line chart with its polynomial coordinate domain made explicit. -/
noncomputable def lineChartMap (b : Bool) : Spec (.of (MvPolynomial LineCoordinate K)) ⟶ grassmannianScheme K 1 1 :=
  grassmannianChartι K (lineChartPermutation b)

lemma lineChartMap_toBase (b : Bool) :
    lineChartMap K b ≫ grassmannianToBase K 1 1 = polynomialSchemeBase K LineCoordinate :=
  grassmannianChartι_toBase K _

instance lineChartMap_open (b : Bool) : IsOpenImmersion (lineChartMap K b) :=
  grassmannianChartι_isOpenImmersion K _

noncomputable def linePairChartMap (a b : Bool) :
    Spec (.of (MvPolynomial PairLineCoordinate K)) ⟶ linePairScheme K :=
  polynomialProductChartMap K LineCoordinate LineCoordinate
    (grassmannianToBase K 1 1) (grassmannianToBase K 1 1)
    (lineChartMap K a) (lineChartMap K b)
    (lineChartMap_toBase K _) (lineChartMap_toBase K _)

lemma linePairChartMap_fst (a b : Bool) :
    linePairChartMap K a b ≫ pullback.fst (grassmannianToBase K 1 1) (grassmannianToBase K 1 1) =
      polynomialSumFirst K LineCoordinate LineCoordinate ≫ lineChartMap K a :=
  polynomialProductChartMap_fst K _ _ _ _ _ _ _ _

lemma linePairChartMap_snd (a b : Bool) :
    linePairChartMap K a b ≫ pullback.snd (grassmannianToBase K 1 1) (grassmannianToBase K 1 1) =
      polynomialSumSecond K LineCoordinate LineCoordinate ≫ lineChartMap K b :=
  polynomialProductChartMap_snd K _ _ _ _ _ _ _ _

lemma linePairChartMap_toBase (a b : Bool) :
    linePairChartMap K a b ≫ linePairToBase K = polynomialSchemeBase K PairLineCoordinate :=
  polynomialProductChartMap_toBase K _ _ _ _ _ _ _ _

instance linePairChartMap_open (a b : Bool) : IsOpenImmersion (linePairChartMap K a b) := by
  unfold linePairChartMap
  infer_instance

lemma linePairCharts_cover (x : linePairScheme K) : ∃ a b y, linePairChartMap K a b y = x := by
  have hc (x : grassmannianScheme K 1 1) :
      ∃ b y, lineChartMap K b y = x := by
    obtain ⟨b, y, hy⟩ := (projectiveLineOpenCover K).exists_eq x
    exact ⟨b.down, y, hy⟩
  exact polynomialProductCharts_cover K LineCoordinate LineCoordinate
    (grassmannianToBase K 1 1) (grassmannianToBase K 1 1)
    (fun b => lineChartMap K b)
    (fun b => lineChartMap K b)
    (fun _ => lineChartMap_toBase K _) (fun _ => lineChartMap_toBase K _) hc hc x

/-- The eight product charts, before renumbering the three polynomial variables. -/
noncomputable def lineTripleProductChartMap (a b c : Bool) :
    Spec (.of (MvPolynomial TripleLineCoordinate K)) ⟶ lineTripleScheme K :=
  polynomialProductChartMap K LineCoordinate PairLineCoordinate
    (grassmannianToBase K 1 1) (linePairToBase K)
    (lineChartMap K a) (linePairChartMap K b c)
    (lineChartMap_toBase K _) (linePairChartMap_toBase K b c)

lemma lineTripleProductChartMap_zero (a b c : Bool) :
    lineTripleProductChartMap K a b c ≫ lineTripleProjection K 0 =
      polynomialSumFirst K LineCoordinate PairLineCoordinate ≫ lineChartMap K a :=
  polynomialProductChartMap_fst K _ _ _ _ _ _ _ _

lemma lineTripleProductChartMap_one (a b c : Bool) :
    lineTripleProductChartMap K a b c ≫ lineTripleProjection K 1 =
      polynomialSumSecond K LineCoordinate PairLineCoordinate ≫
        polynomialSumFirst K LineCoordinate LineCoordinate ≫ lineChartMap K b := by
  change lineTripleProductChartMap K a b c ≫ (pullback.snd _ _ ≫ pullback.fst _ _) = _
  rw [← Category.assoc]
  rw [show lineTripleProductChartMap K a b c ≫ pullback.snd _ _ =
    polynomialSumSecond K LineCoordinate PairLineCoordinate ≫ linePairChartMap K b c from
      polynomialProductChartMap_snd K _ _ _ _ _ _ _ _]
  rw [Category.assoc, linePairChartMap_fst]

lemma lineTripleProductChartMap_two (a b c : Bool) :
    lineTripleProductChartMap K a b c ≫ lineTripleProjection K 2 =
      polynomialSumSecond K LineCoordinate PairLineCoordinate ≫
        polynomialSumSecond K LineCoordinate LineCoordinate ≫ lineChartMap K c := by
  change lineTripleProductChartMap K a b c ≫ (pullback.snd _ _ ≫ pullback.snd _ _) = _
  rw [← Category.assoc]
  rw [show lineTripleProductChartMap K a b c ≫ pullback.snd _ _ =
    polynomialSumSecond K LineCoordinate PairLineCoordinate ≫ linePairChartMap K b c from
      polynomialProductChartMap_snd K _ _ _ _ _ _ _ _]
  rw [Category.assoc, linePairChartMap_snd]

lemma lineTripleProductChartMap_toBase (a b c : Bool) :
    lineTripleProductChartMap K a b c ≫ lineTripleToBase K = polynomialSchemeBase K TripleLineCoordinate :=
  polynomialProductChartMap_toBase K _ _ _ _ _ _ _ _

instance lineTripleProductChartMap_open (a b c : Bool) : IsOpenImmersion (lineTripleProductChartMap K a b c) := by
  unfold lineTripleProductChartMap
  infer_instance

lemma lineTripleProductCharts_cover (x : lineTripleScheme K) :
    ∃ a b c y, lineTripleProductChartMap K a b c y = x := by
  have hc (x : grassmannianScheme K 1 1) :
      ∃ b y, lineChartMap K b y = x := by
    obtain ⟨b, y, hy⟩ := (projectiveLineOpenCover K).exists_eq x
    exact ⟨b.down, y, hy⟩
  have hd (y : linePairScheme K) : ∃ bc : Bool × Bool, ∃ z, linePairChartMap K bc.1 bc.2 z = y := by
    obtain ⟨b, c, z, hz⟩ := linePairCharts_cover K y
    exact ⟨(b, c), z, hz⟩
  obtain ⟨a, ⟨b, c⟩, y, hy⟩ := polynomialProductCharts_cover K LineCoordinate PairLineCoordinate
    (grassmannianToBase K 1 1) (linePairToBase K)
    (fun a => lineChartMap K a)
    (fun bc : Bool × Bool => linePairChartMap K bc.1 bc.2)
    (fun _ => lineChartMap_toBase K _) (fun bc => linePairChartMap_toBase K bc.1 bc.2) hc hd x
  exact ⟨a, b, c, y, hy⟩

end
end PfaffianDescent
