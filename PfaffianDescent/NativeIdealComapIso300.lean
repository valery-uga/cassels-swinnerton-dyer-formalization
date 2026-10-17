import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- A genuine presentation Iso reflects WHOLE ideal pullback equality. -/
lemma nativeIdealComapIso_injective300 {X Y : Scheme.{u}} (e : X ≅ Y)
    (I J : Y.IdealSheafData) (h : I.comap e.hom = J.comap e.hom) : I = J := by
  have hh := congrArg (fun K : X.IdealSheafData => K.comap e.inv) h
  simpa only [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
    Scheme.IdealSheafData.comap_id] using hh

end PfaffianDescent
