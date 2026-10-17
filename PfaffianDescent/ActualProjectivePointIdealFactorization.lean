import PfaffianDescent.HomogeneousQuotientMap
import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.ProjectivePointCoordinates

/-! SOURCE ONLY / UNVERIFIED. Factor the SAME field-valued projective point
through another homogeneous ideal once its actual normalized chart coordinates
annihilate that ideal. The ambient morphism equality is proved, not supplied.
The generic equation hypothesis is discharged by the chosen-secant caller. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {R E : Type u} [CommRing R] [Field E] {s : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two maps of one actual coordinate chart agree if their coefficient and
normalized-coordinate values agree. -/
theorem actualCoordinateChartHom_ext
    (I : HomogeneousIdeal (homogeneousSubmodule s R)) (j : s)
    (g h : ChartRing I j →+* E)
    (hb : g.comp (chartBaseMap I j) = h.comp (chartBaseMap I j))
    (hx : ∀ m, g (chartCoordinate I j m) = h (chartCoordinate I j m)) : g = h := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j z
  change g (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
    h (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))
  rw [hom_eval₂, hom_eval₂, hb]
  congr 1
  exact funext hx

/-- The factor retains the given chart point and its literal ambient embedding.
No reduced-support or existence-only coordinate comparison is used. -/
theorem actualProjectivePoint_factors_of_chart_equations
    (I J : HomogeneousIdeal (homogeneousSubmodule s R))
    (f : R →+* E) (j : s) (g : ChartRing I j →+* E)
    (hb : g.comp (chartBaseMap I j) = f)
    (hJ : ∀ p ∈ J.toIdeal,
      p.eval₂ f (fun m => g (chartCoordinate I j m)) = 0) :
    ∃ b : Spec (.of E) ⟶ scheme J,
      b ≫ toBase J = Spec.map (CommRingCat.ofHom f) ∧
      b ≫ quotientProjMap J =
        (Spec.map (CommRingCat.ofHom g) ≫ chartι I j) ≫ quotientProjMap I := by
  classical
  let x : s → E := fun m => g (chartCoordinate I j m)
  let H := I ⊔ J
  have hIH : I.toIdeal ≤ H.toIdeal := le_sup_left
  have hJH : J.toIdeal ≤ H.toIdeal := le_sup_right
  have hI : I.toIdeal ≤ RingHom.ker (eval₂Hom f x) := by
    intro p hp
    have he := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hp)
    change p.eval₂ f x = 0
    simpa only [hom_eval₂, hb, map_zero, x] using he
  have hJ' : J.toIdeal ≤ RingHom.ker (eval₂Hom f x) := hJ
  have hH : H.toIdeal ≤ RingHom.ker (eval₂Hom f x) := sup_le hI hJ'
  let e : CoordinateRing H →+* E :=
    Ideal.Quotient.lift H.toIdeal (eval₂Hom f x) hH
  have hxj : x j = 1 := by simp only [x, chartCoordinate_self, map_one]
  have heOne : e (coordinate H j) = 1 := by
    change (X j : MvPolynomial s R).eval₂ f x = 1
    rw [eval₂_X, hxj]
  let h : ChartRing H j →+* E :=
    AllCharacteristics.GradedChart.liftCoordinateOne (grading H) (coordinate H j) e heOne
  have hbase : h.comp (chartBaseMap H j) = f := by
    ext r
    exact (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap
      (grading H) (coordinate H j) e heOne r).trans (eval₂_C f x r)
  have hcoord (m : s) : h (chartCoordinate H j m) = x m := by
    exact (AllCharacteristics.GradedChart.liftCoordinateOne_normalized
      (grading H) (coordinate H j) e heOne (coordinate_mem H j)
      (coordinate H m) (coordinate_mem H m)).trans (eval₂_X f x m)
  have hcomp : h.comp (chartQuotientMap I H hIH j) = g := by
    apply actualCoordinateChartHom_ext I j
    · ext r
      change h (chartQuotientMap I H hIH j (chartBaseMap I j r)) =
        g (chartBaseMap I j r)
      exact (congrArg h (RingHom.congr_fun
        (chartQuotientMap_chartBaseMap I H hIH j) r)).trans
          ((RingHom.congr_fun hbase r).trans (RingHom.congr_fun hb r).symm)
    · intro m
      rw [RingHom.comp_apply, chartQuotientMap_chartCoordinate]
      exact hcoord m
  let bH : Spec (.of E) ⟶ scheme H :=
    Spec.map (CommRingCat.ofHom h) ≫ chartι H j
  have hbH : bH ≫ toBase H = Spec.map (CommRingCat.ofHom f) := by
    dsimp only [bH]
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
    exact congrArg (fun t : R →+* E => Spec.map (CommRingCat.ofHom t)) hbase
  have hbHI : bH ≫ schemeQuotientMap I H hIH =
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j := by
    dsimp only [bH]
    rw [Category.assoc, chartι_schemeQuotientMap, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun t : ChartRing I j →+* E =>
      Spec.map (CommRingCat.ofHom t) ≫ chartι I j) hcomp
  let b := bH ≫ schemeQuotientMap J H hJH
  refine ⟨b, ?_, ?_⟩
  · dsimp only [b]
    rw [Category.assoc, schemeQuotientMap_toBase]
    exact hbH
  · dsimp only [b]
    rw [Category.assoc, schemeQuotientMap_comp_quotientProjMap,
      ← schemeQuotientMap_comp_quotientProjMap I H hIH, ← Category.assoc, hbHI]

end PfaffianDescent
