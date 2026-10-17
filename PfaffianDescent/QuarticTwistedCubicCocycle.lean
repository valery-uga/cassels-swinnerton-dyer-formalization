import PfaffianDescent.QuarticTwistedCubicSymmetricCube

namespace PfaffianDescent
namespace QuarticNet

open scoped MatrixGroups
open Matrix

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

/-- The action on a projective linear group induced by a field automorphism. -/
noncomputable def projectiveFieldAction (n : ℕ) (rho : G →* L ≃+* L)
    (g : G) : PGL(Fin n, L) →* PGL(Fin n, L) :=
  Matrix.ProjGenLinGroup.map (rho g).toRingHom

/-- A projective Galois cocycle for an `n`-dimensional projective space. -/
structure ProjectiveCocycle (n : ℕ) (rho : G →* L ≃+* L) where
  toFun : G → PGL(Fin n, L)
  map_one' : toFun 1 = 1
  map_mul' : ∀ g h, toFun (g * h) =
    toFun g * projectiveFieldAction n rho g (toFun h)

namespace ProjectiveCocycle

instance {n rho} : CoeFun (ProjectiveCocycle (L := L) (G := G) n rho)
    (fun _ => G → PGL(Fin n, L)) := ⟨ProjectiveCocycle.toFun⟩

/-- A cocycle is a coboundary when its projective descent datum is split. -/
def IsCoboundary {n : ℕ} {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) n rho) : Prop :=
  ∃ x : PGL(Fin n, L), ∀ g,
    c g = x⁻¹ * projectiveFieldAction n rho g x

/-- Cubic symmetric powers carry projective cocycles on a line to projective
cocycles on the ambient three-space. -/
noncomputable def symmetricCube {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) : ProjectiveCocycle (L := L) 4 rho where
  toFun g := symmetricCubePGL (c g)
  map_one' := by
    rw [c.map_one']
    exact map_one _
  map_mul' g h := by
    rw [c.map_mul', map_mul]
    congr 1
    symm
    exact symmetricCubePGL_map (rho g).toRingHom (c h)

/-- A cubic symmetric power of a projective coboundary is again a
coboundary. -/
theorem symmetricCube_isCoboundary {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (hc : c.IsCoboundary) :
    (symmetricCube c).IsCoboundary := by
  obtain ⟨x, hx⟩ := hc
  refine ⟨symmetricCubePGL x, ?_⟩
  intro g
  change symmetricCubePGL (c g) =
    (symmetricCubePGL x)⁻¹ * projectiveFieldAction 4 rho g (symmetricCubePGL x)
  rw [hx g, map_mul, map_inv]
  congr 1
  symm
  exact symmetricCubePGL_map (rho g).toRingHom x

end ProjectiveCocycle
end QuarticNet
end PfaffianDescent
