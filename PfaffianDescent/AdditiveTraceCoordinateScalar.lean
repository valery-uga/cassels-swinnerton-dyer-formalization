import PfaffianDescent.ExtPullbackTraceCoordinate

/-! # Transporting a checked scalar action through a trace coordinate -/
noncomputable section
namespace PfaffianDescent
universe u v w

/-- Scalar compatibility of both actual maps implies scalar compatibility of
their coordinate trace. The actions are arbitrary functions, so all geometric
and field-scalar identifications are supplied by the caller's checked theorems. -/
theorem additiveTraceCoordinateAddHom_map_action
    {A : Type u} [AddCommGroup A] {L : Type v} [AddCommGroup L]
    {K : Type w} [AddCommGroup K]
    (e : A ≃+ L) (tr : A →+ K)
    (sA : A → A) (sL : L → L) (sK : K → K)
    (he : ∀ z, e (sA z) = sL (e z))
    (htr : ∀ z, tr (sA z) = sK (tr z)) (a : L) :
    additiveTraceCoordinateAddHom e tr (sL a) =
      sK (additiveTraceCoordinateAddHom e tr a) := by
  have ha : e (sA (e.symm a)) = sL a :=
    (he (e.symm a)).trans (congrArg sL (e.apply_symm_apply a))
  calc
    additiveTraceCoordinateAddHom e tr (sL a) =
        additiveTraceCoordinateAddHom e tr (e (sA (e.symm a))) :=
      congrArg (additiveTraceCoordinateAddHom e tr) ha.symm
    _ = tr (sA (e.symm a)) :=
      additiveTraceCoordinateAddHom_evaluate_class e tr _
    _ = sK (tr (e.symm a)) := htr _
    _ = sK (additiveTraceCoordinateAddHom e tr a) := rfl

end PfaffianDescent
