import PfaffianDescent.NativeWholeIdealComparisonDescent300
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- A literal closed chart is the actual pullback of the global closed ideal.
Both isomorphisms are constructed natively from the whole kernel equality. -/
def nativeClosedChartPullbackIso312
    {X U V : Scheme.{u}} (I : X.IdealSheafData) (a : U ⟶ X) (q : V ⟶ U)
    [IsClosedImmersion q] (h : I.comap a = q.ker) :
    V ≅ pullback a I.subschemeι :=
  asIso q.toImage ≪≫ nativeClosedIdealComparisonIso300 I a q.ker h

lemma nativeClosedChartPullbackIso_hom_fst312
    {X U V : Scheme.{u}} (I : X.IdealSheafData) (a : U ⟶ X) (q : V ⟶ U)
    [IsClosedImmersion q] (h : I.comap a = q.ker) :
    (nativeClosedChartPullbackIso312 I a q h).hom ≫ pullback.fst a I.subschemeι = q := by
  rw [nativeClosedChartPullbackIso312, Iso.trans_hom, Category.assoc,
    nativeClosedIdealComparisonIso_hom_fst300]
  exact q.toImage_imageι

def nativeClosedChartToGlobal312
    {X U V : Scheme.{u}} (I : X.IdealSheafData) (a : U ⟶ X) (q : V ⟶ U)
    [IsClosedImmersion q] (h : I.comap a = q.ker) : V ⟶ I.subscheme :=
  (nativeClosedChartPullbackIso312 I a q h).hom ≫ pullback.snd a I.subschemeι

lemma nativeClosedChartToGlobal_comp312
    {X U V : Scheme.{u}} (I : X.IdealSheafData) (a : U ⟶ X) (q : V ⟶ U)
    [IsClosedImmersion q] (h : I.comap a = q.ker) :
    nativeClosedChartToGlobal312 I a q h ≫ I.subschemeι = q ≫ a := by
  rw [nativeClosedChartToGlobal312, Category.assoc, ← pullback.condition,
    ← Category.assoc, nativeClosedChartPullbackIso_hom_fst312]

lemma nativeClosedChartToGlobal_isPullback312
    {X U V : Scheme.{u}} (I : X.IdealSheafData) (a : U ⟶ X) (q : V ⟶ U)
    [IsClosedImmersion q] (h : I.comap a = q.ker) :
    IsPullback q (nativeClosedChartToGlobal312 I a q h) a I.subschemeι := by
  apply IsPullback.of_iso_pullback
    ⟨(nativeClosedChartToGlobal_comp312 I a q h).symm⟩
    (nativeClosedChartPullbackIso312 I a q h)
  · exact nativeClosedChartPullbackIso_hom_fst312 I a q h
  · rfl

/-- Canonical polynomial-chart lifting through a base change is formed
before any actual coefficient localization or quotient is substituted. -/
def nativeCartesianBaseChangeChartMap312
    {P T E H L : Scheme.{u}} (a : P ⟶ E) (v : P ⟶ T) (g : T ⟶ L)
    (F : E ⟶ H) (i : L ⟶ H) (h : IsPullback a v F (g ≫ i)) :
    P ⟶ pullback F i :=
  pullback.lift a (v ≫ g) (h.w.trans (Category.assoc v g i).symm)

lemma nativeCartesianBaseChangeChartMap_fst312
    {P T E H L : Scheme.{u}} (a : P ⟶ E) (v : P ⟶ T) (g : T ⟶ L)
    (F : E ⟶ H) (i : L ⟶ H) (h : IsPullback a v F (g ≫ i)) :
    nativeCartesianBaseChangeChartMap312 a v g F i h ≫ pullback.fst F i = a := by
  simp only [nativeCartesianBaseChangeChartMap312, pullback.lift_fst]

lemma nativeCartesianBaseChangeChartMap_snd312
    {P T E H L : Scheme.{u}} (a : P ⟶ E) (v : P ⟶ T) (g : T ⟶ L)
    (F : E ⟶ H) (i : L ⟶ H) (h : IsPullback a v F (g ≫ i)) :
    nativeCartesianBaseChangeChartMap312 a v g F i h ≫ pullback.snd F i = v ≫ g := by
  simp only [nativeCartesianBaseChangeChartMap312, pullback.lift_snd]

/-- The lifted chart is actually Cartesian over the new base. -/
lemma nativeCartesianBaseChangeChartMap_isPullback312
    {P T E H L : Scheme.{u}} (a : P ⟶ E) (v : P ⟶ T) (g : T ⟶ L)
    (F : E ⟶ H) (i : L ⟶ H) (h : IsPullback a v F (g ≫ i)) :
    IsPullback (nativeCartesianBaseChangeChartMap312 a v g F i h) v
      (pullback.snd F i) g := by
  have houter : IsPullback v
      (nativeCartesianBaseChangeChartMap312 a v g F i h ≫ pullback.fst F i)
      (g ≫ i) F := by
    rw [nativeCartesianBaseChangeChartMap_fst312]
    exact h.flip
  exact (houter.of_bot (nativeCartesianBaseChangeChartMap_snd312 a v g F i h).symm
    (IsPullback.of_hasPullback F i).flip).flip

end PfaffianDescent
end
