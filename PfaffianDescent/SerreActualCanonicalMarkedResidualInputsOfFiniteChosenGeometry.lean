import PfaffianDescent.SerreActualCanonicalMarkedResidualInputsOfFiniteChosenSeed
import PfaffianDescent.SerreActualChosenMarkedResidualGeometry

/-! Convert one actual chosen-geometry record to canonical marked residual
inputs. Keeping its dependent projections abstract avoids reducing a native
section factory separately for each field. Finiteness remains the actual
chosen fibre's finiteness, derived by the native caller from its old good seed. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

@[irreducible]
def serreActualCanonicalMarkedResidualInputsOfFiniteChosenGeometry
    {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E]
    {X P Z I : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp) [IsClosedImmersion zero]
    [IsProper (zero ≫ pullback.snd x pp)]
    (i : I ⟶ X) (j : Spec (.of L) ⟶ X)
    (tE : Spec (.of E) ⟶ P)
    [Finite (pullback (zero ≫ pullback.snd x pp) tE : Scheme.{u})]
    (d : SerreActualChosenMarkedResidualGeometry x pp zero i j tE) :
    SerreActualCanonicalMarkedResidualInputs (E := E) (Cfg := Spec (.of E))
      x pp zero i j :=
  serreActualCanonicalMarkedResidualInputsOfFiniteChosenSeed x pp zero i j
    d.t d.ht tE d.htE d.δ d.hδ d.n d.hout d.hpoint d.y d.hy d.hySurface

end PfaffianDescent
