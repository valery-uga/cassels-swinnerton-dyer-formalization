import AllCharacteristics.ProjectiveTupleQuotientAction
import AllCharacteristics.RelativeGlobalQuotientChartPullback

/-!
# Affine quotient charts around field-valued ordered tuples

An ordered tuple over a field lies in one common affine chart.  If its image
in the global unordered-tuple quotient descends to the ground field, that
ground-field point lies in the corresponding affine invariant-quotient
chart as well.  The ordered lift and its quotient equation therefore factor
through one concrete affine quotient.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u v

variable {A : Type u} [CommRing A]
variable {sigma : Type v} [SetLike sigma A] [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable {S : Scheme.{u}} [IsAffine S]
variable (f : Proj graded ⟶ S) (n : ℕ)

/-- A field-valued ordered lift of a descended unordered projective tuple
can be placed, together with the descended point, in one actual affine
invariant-quotient chart. -/
theorem exists_projectiveTuple_fieldPoint_affineChart
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Spec (.of K) ⟶ S)
    (c : Spec (.of K) ⟶ projectiveOrderedTupleQuotient graded f n)
    (hc : c ≫ projectiveOrderedTupleQuotientToBase graded f n = b)
    (a : Spec (.of L) ⟶ (orderedFamilyPowerOver f n).left)
    (hquot : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ c =
      a ≫ projectiveOrderedTupleQuotientMap graded f n) :
    ∃ (U : (Proj graded).affineOpens)
      (aU : Spec (.of L) ⟶ (orderedFamilyCommonOpen f U.val n).toScheme)
      (cU : Spec (.of K) ⟶ commonOpenTupleQuotient f U.val n),
      aU ≫ (orderedFamilyCommonOpen f U.val n).ι = a ∧
      cU ≫ commonOpenTupleQuotientGluedChart f n U = c ∧
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ cU =
      aU ≫ commonOpenTupleQuotientMap f U.val n U.property ∧
      cU ≫ commonOpenTupleQuotientToBase f U.val n = b := by
  letI : (Proj graded).IsSeparated := inferInstance
  let pi : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let x : (orderedFamilyPowerOver f n).left :=
    a (IsLocalRing.closedPoint L)
  obtain ⟨U, hxU⟩ :=
    exists_commonAffineOpen_orderedProjectivePoint graded f n x
  let H := orderedFamilyCommonOpen f U.val n
  let i : H.toScheme ⟶ (orderedFamilyPowerOver f n).left := H.ι
  have harange : Set.range a ⊆ Set.range i := by
    rintro y ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    subst z
    exact ⟨⟨x, hxU⟩, rfl⟩
  let aU : Spec (.of L) ⟶ H.toScheme :=
    IsOpenImmersion.lift i a harange
  have haU : aU ≫ i = a := IsOpenImmersion.lift_fac i a harange
  let qU : H.toScheme ⟶ commonOpenTupleQuotient f U.val n :=
    commonOpenTupleQuotientMap f U.val n U.property
  let j : commonOpenTupleQuotient f U.val n ⟶
      projectiveOrderedTupleQuotient graded f n :=
    commonOpenTupleQuotientGluedChart f n U
  have hchart : i ≫ projectiveOrderedTupleQuotientMap graded f n = qU ≫ j := by
    exact projectiveOrderedTupleQuotientMap_chart graded f n U
  haveI : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (commonOpenTupleQuotientGluedChart f n U))
  have hcrange : Set.range c ⊆ Set.range j := by
    rintro y ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst z
    refine ⟨qU (aU (IsLocalRing.closedPoint L)), ?_⟩
    have hquotPoint := congrArg
      (fun m : Spec (.of L) ⟶ projectiveOrderedTupleQuotient graded f n ↦
        m (IsLocalRing.closedPoint L)) hquot
    have hpi : pi (IsLocalRing.closedPoint L) =
        IsLocalRing.closedPoint K := Subsingleton.elim _ _
    change c (pi (IsLocalRing.closedPoint L)) =
      projectiveOrderedTupleQuotientMap graded f n
        (a (IsLocalRing.closedPoint L)) at hquotPoint
    rw [hpi] at hquotPoint
    have haUPoint : i (aU (IsLocalRing.closedPoint L : Spec (.of L))) =
        a (IsLocalRing.closedPoint L) :=
      congrArg
        (fun m : Spec (.of L) ⟶ (orderedFamilyPowerOver f n).left ↦
          m (IsLocalRing.closedPoint L)) haU
    calc
      j (qU (aU (IsLocalRing.closedPoint L))) =
          projectiveOrderedTupleQuotientMap graded f n
            (i (aU (IsLocalRing.closedPoint L))) := by
        exact (congrArg
          (fun m : H.toScheme ⟶ projectiveOrderedTupleQuotient graded f n ↦
            m (aU (IsLocalRing.closedPoint L))) hchart).symm
      _ = projectiveOrderedTupleQuotientMap graded f n
          (a (IsLocalRing.closedPoint L)) := congrArg _ haUPoint
      _ = c (IsLocalRing.closedPoint K) := hquotPoint.symm
  let cU : Spec (.of K) ⟶ commonOpenTupleQuotient f U.val n :=
    IsOpenImmersion.lift j c hcrange
  have hcU : cU ≫ j = c := IsOpenImmersion.lift_fac j c hcrange
  have hlocal : pi ≫ cU = aU ≫ qU := by
    apply (cancel_mono j).mp
    calc
      (pi ≫ cU) ≫ j = pi ≫ c := by rw [Category.assoc, hcU]
      _ = a ≫ projectiveOrderedTupleQuotientMap graded f n := hquot
      _ = (aU ≫ i) ≫ projectiveOrderedTupleQuotientMap graded f n := by rw [haU]
      _ = aU ≫ (i ≫ projectiveOrderedTupleQuotientMap graded f n) :=
        Category.assoc _ _ _
      _ = aU ≫ (qU ≫ j) := by rw [hchart]
      _ = (aU ≫ qU) ≫ j := (Category.assoc _ _ _).symm
  have hcUbase : cU ≫ commonOpenTupleQuotientToBase f U.val n = b := by
    rw [← commonOpenTupleQuotientGluedChart_toBase f n U,
      ← Category.assoc]
    change (cU ≫ j) ≫ projectiveOrderedTupleQuotientToBase graded f n = b
    rw [hcU]
    exact hc
  exact ⟨U, aU, cU, haU, hcU, hlocal, hcUbase⟩

end AllCharacteristics
