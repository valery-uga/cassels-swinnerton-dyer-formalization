import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

variable {H Y U Q S : Scheme.{u}}
variable (g : H ⟶ S) (f : Y ⟶ S) (i : U ⟶ H) (b : U ⟶ S)
variable (hi : i ≫ g = b) (r : Q ⟶ Y) (q : Q ⟶ U) (hQ : IsPullback r q f b)

/-- Actual lift into the original global ambient pullback, with its square derived locally. -/
def nativeAmbientChartLift300 : Q ⟶ pullback g f :=
  pullback.lift (q ≫ i) r (by rw [Category.assoc, hi]; exact hQ.w.symm)

lemma nativeAmbientChartLift_fst300 :
    nativeAmbientChartLift300 g f i b hi r q hQ ≫ pullback.fst g f = q ≫ i :=
  pullback.lift_fst _ _ _

lemma nativeAmbientChartLift_snd300 :
    nativeAmbientChartLift300 g f i b hi r q hQ ≫ pullback.snd g f = r :=
  pullback.lift_snd _ _ _

/-- Cancellation of the actual global Cartesian square identifies the native local chart. -/
lemma nativeAmbientChartLift_isPullback300 :
    IsPullback (nativeAmbientChartLift300 g f i b hi r q hQ) q (pullback.fst g f) i := by
  apply IsPullback.of_right (h₁₂ := pullback.snd g f) (h₂₂ := g)
  · rw [nativeAmbientChartLift_snd300, hi]
    exact hQ
  · exact nativeAmbientChartLift_fst300 g f i b hi r q hQ
  · exact (IsPullback.of_hasPullback g f).flip

/-- An ordinary actual pullback domain stays Cartesian after its domain presentation Iso. -/
lemma nativePullbackDomainIso300
    {P X Y Z P' : Scheme.{u}} {a : P ⟶ X} {c : P ⟶ Y} {s : X ⟶ Z} {t : Y ⟶ Z}
    (h : IsPullback a c s t) (e : P' ≅ P) :
    IsPullback (e.hom ≫ a) (e.hom ≫ c) s t := by
  apply h.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  all_goals simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The actual native gluing intersection is Cartesian, before any coefficient rings are used. -/
lemma nativeSchemeGlueData_pairIsPullback300 (D : Scheme.GlueData.{u}) (i j : D.J) :
    IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
  IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)

/-- Cartesian polynomial charts over an actual Cartesian base overlap give the
true ambient chart overlap. No desired ambient-square premise is needed. -/
lemma nativeAmbientOverlap_isPullback300
    {P Qi Qj X Ui Uj V H : Scheme.{u}}
    (pi : P ⟶ Qi) (pj : P ⟶ Qj) (q : P ⟶ V)
    (qi : Qi ⟶ Ui) (qj : Qj ⟶ Uj) (vi : V ⟶ Ui) (vj : V ⟶ Uj)
    (ai : Qi ⟶ X) (aj : Qj ⟶ X) (p : X ⟶ H) (ui : Ui ⟶ H) (uj : Uj ⟶ H)
    (hpi : IsPullback pi q qi vi) (hpj : IsPullback pj q qj vj)
    (hV : IsPullback vi vj ui uj) (hj : IsPullback aj qj p uj)
    (hi : ai ≫ p = qi ≫ ui) (hw : pi ≫ ai = pj ≫ aj) :
    IsPullback pi pj ai aj := by
  have houter : IsPullback pi (pj ≫ qj) (ai ≫ p) uj := by
    rw [hpj.w, hi]
    exact hpi.paste_vert hV
  exact houter.of_bot hw hj

end PfaffianDescent
