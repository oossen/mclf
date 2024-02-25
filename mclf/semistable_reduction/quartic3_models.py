
"""
Semistable models of plane quartic curves at `p=3`
==================================================
"""

from sage.all import ZZ, QQ, FunctionField, SageObject, Infinity
from sage.geometry.newton_polygon import NewtonPolygon
from sage.functions.other import *
from mclf.berkovich.berkovich_line import *
from mclf.berkovich.affinoid_domain import *
from mclf.berkovich.piecewise_affine_functions import *
from mclf.curves.smooth_projective_curves import *
from mclf.semistable_reduction.reduction_trees import ReductionTree
from mclf.semistable_reduction.semistable_models import SemistableModel



class Quartic3Model(SemistableModel):
	"""
	Return a semistable model of a plane quartic curve.

	INPUT:

	- ``Y`` -- a plane quartic curve over a field `K`
	- ``vK`` -- a discrete valuation on `K`

	OUTPUT: the object representing a semistable model of `Y`. 

	EXAMPLES: 

	::

		sage: from mclf import *
		sage: vK = QQ.valuation(3)
		sage: R.<x,y> = QQ[]
		sage: F = y^3 + x^3*y + x^4 + 1
		sage: Y = SmoothProjectiveCurve(F)
		sage: M = Quartic3Model(Y, vK)
		sage: M.is_semistable()
		True

	"""

	def __init__(self, Y, vK):

		assert Y.covering_degree() == 3, "the covering is not of degree 3"
		assert vK.residue_field().characteristic() == 3, "this class is only for reduction at 3"

		Delta = Y.function_field().polynomial().discriminant().numerator()
		NP = npolygon(Delta, 0, vK)
		s = ceil(max(NP.slopes()))
		if s > 0:
			FX = Y.rational_function_field()
			FY = Y.function_field()
			R = FX.constant_base_field()[FX.variable_name(), FY.variable_name()]
			x = R.gens()[0]
			y = R.gens()[1]
			F = R(FY.polynomial())
			pi = vK.uniformizer()**(vK(vK.uniformizer()).denominator()) #now v(pi)=1
			F = F(x=x/pi**s, y=y/pi**(2*s))*pi**(6*s)
			Y = SmoothProjectiveCurve(F)
			print("We do a base change so that the branch locus is integral and now consider", Y)
		self._scaling_factor = s

		self._curve = Y
		self._FY = Y.function_field()
		self._FX = Y.rational_function_field()
		self._K = self._FX.constant_base_field()
		self._base_valuation = vK
		self._X = BerkovichLine(self._FX, self._base_valuation)


	def reduction_tree(self):

		TL = self.tail_locus()
		print("The tail locus is the", TL)
		X = self._X
		T = BerkovichTree(X)
		T.add_point(X.gauss_point())
		for xi in TL.boundary():
			T.add_point(xi)
		v = self._base_valuation
		Y = self._curve
		R = ReductionTree(Y, v, T)
		print("Components coming from tail disks are")
		tail_genus = 0

		# we skip over the Gauss point, we just added it so there isn't any problems with adding points later
		for I in R.inertial_components()[1:]:
			print([U.component() for U in I.upper_components()])
			tail_genus += sum([U.component().genus() for U in I.upper_components()])
		print("The contribution of the tail disks to the arithmetic genus is", tail_genus)

		if tail_genus == 3:
			print("We are done!")
			return R

		V = self.tame_locus()
		FY = self._FY
		Delta = FY.polynomial().discriminant()
		T_Delta = BerkovichTree(X)
		T_Delta = T_Delta.adapt_to_function(Delta)
		T_Delta.permanent_completion()
		print("The entire tame locus is the", V)
		for xi in V.boundary():
			if any([leaf.root().discoid()[0].degree() > 3 and leaf.parent().root().is_strictly_less(xi) and xi.is_strictly_less(leaf.root()) for leaf in T_Delta.leaves(subtrees=True)]):
				print("The boundary point", xi, "can't contribute to the arithmetic genus")
			else:
				T.add_point(xi)
		R = ReductionTree(Y, v, T)
		abelian_genus = 0
		for I in R.inertial_components():
			abelian_genus += sum([U.component().genus() for U in I.upper_components()])
		print("The total contribution to the arithmetic genus from boundary points of the tame locus is", abelian_genus)

		if abelian_genus == 3:
			print("We are done!")
			return R

		missing_genus = 3 - abelian_genus
		print("We take loops into account now")
		T = BerkovichTree(X)
		T.add_point(X.gauss_point())
		for xi in V.boundary():
			if any([leaf.root().discoid()[0].degree() > missing_genus and leaf.parent().root().is_strictly_less(xi) and xi.is_strictly_less(leaf.root()) for leaf in T_Delta.leaves(subtrees=True)]):
				print("The boundary point", xi, "can't contribute to the arithmetic genus")
			else:
				T.add_point(xi)
		R = ReductionTree(Y, v, T)
		print("Now the genus is", R.reduction_genus())
		if R.reduction_genus() == 3:
			print("We are done!")
			return R

		print("We make sure branch points are separated")
		for xi in [xi for xi in T_Delta.vertices() if V.is_in(xi)]:
			T.add_point(xi)
		R = ReductionTree(Y, v, T)
		print("Now the reduction genus is", R.reduction_genus())

		assert R.reduction_genus() == 3, "We are not done"
		print("We are done!")
		return R

	def discriminant_tree(self):

		X = self._X
		FY = self._FY
		Delta = FY.polynomial().discriminant()
		T = BerkovichTree(X)
		T = T.adapt_to_function(Delta)
		T.permanent_completion()
		return T


	def tame_locus(self):

		if not hasattr(self, "_tame_locus"):
			self._tame_locus = UnionOfDomains([self.interior_locus(), self.potential_tail_locus()])
		return self._tame_locus    

	def rescaled_tame_locus(self):

		if self._scaling_factor == 0:
			return self.tame_locus()
		if hasattr(self, "_rescaled_tame_locus"):
			return self._rescaled_tame_locus
		X = self._X
		AT = self.tame_locus().tree()
		AT_rescaled = AffinoidTree(X, root = AT.vertices()[0], is_in = AT.is_in(AT.vertices()[0]))
		for xi in AT.vertices()[1:]:
			print(AT_rescaled.vertices())
			print(xi)
			psi, s = xi.discoid()
			psi = psi.numerator()
			x = self._FX.gen()
			vK = self._base_valuation
			pi = vK.uniformizer()**(vK(vK.uniformizer()).denominator())
			degree = psi.degree()
			new_psi = self._FX(psi(x*pi**(self._scaling_factor)).numerator().monic())

			new_xi = X.point_from_discoid(new_psi, s - self._scaling_factor*degree)
			if new_xi.is_gauss_point():
				continue
			new_xi_in = AT.is_in(xi)
			target, target_tree, lower_target, target_vertex = AT_rescaled.position(new_xi)
			new_xi_tree = AffinoidTree(X, root=new_xi, is_in = new_xi_in)
			if not target_vertex:
				new_lower_target = AffinoidTree(X, target, [lower_target, new_xi_tree], target_tree, AT_rescaled.is_in(target))
				lower_target.make_parent(new_lower_target)
				lower_target_index = target_tree._children.index(lower_target)
				target_tree._children[lower_target_index] = new_lower_target
			else:
				target_tree.make_child(new_xi_tree)
				new_xi_tree.make_parent(target_tree)

		self._rescaled_tame_locus = AffinoidDomainOnBerkovichLine(AT_rescaled)
		return self._rescaled_tame_locus


	

	def tail_locus(self):

		if hasattr(self, "_tail_locus"):
			return self._tail_locus

		TL = self.potential_tail_locus()
		IL = self.interior_locus()

		components = [comp for comp in TL.components() if any([TL.is_in(xi) and not IL.is_in(xi) for xi in comp.tree().vertices()])]
		if not len(components) == 0:
			self._tail_locus = UnionOfDomains(components)
		else:
			X = self._X
			self._tail_locus = AffinoidDomainOnBerkovichLine(AffinoidTree(X))
		return self._tail_locus


	def interior_locus(self):
		r"""
		Return the image of the *interior locus* under the map `\varphi\colon Y\to X`.

		It is an affinoid subdomain of `X^{\textrm{an}}`.

		"""

		if hasattr(self, "_interior_locus"):
			return self._interior_locus

		Y = self._curve
		FY = self._FY
		FX = self._FX
		K = self._K
		v = self._base_valuation
		X = self._X

		Delta = FY.polynomial().discriminant()
		mu_locus_AT = AffinoidTree(X, root = X.gauss_point())

		first_leaf = True
		for factor, _ in Delta.numerator().factor():
			L = K.extension(factor, 'a')
			a = L.gen()
			
			R = L[FX.variable_name(), FY.variable_name()]
			x = R.gens()[0]
			y = R.gens()[1]
			Y_poly = FY.polynomial()
			F0 = sum([y**i*sum([x**j*Y_poly[i].numerator()[j] for j in range(Y_poly[i].numerator().degree()+1)]) for i in range(Y_poly.degree()+1)])
			F = F0.subs({x:a,y:y}).univariate_polynomial()
			assert len(F.roots()) > 0, "there is no rational point above"
			b = F.roots()[0][0]
			G = F0.subs({x:x+a,y:y+b})
			a1 = G.monomial_coefficient(x*y**2)
			b2 = G.monomial_coefficient(x**2*y)
			c3 = G.monomial_coefficient(x**3)

			R = L['u']
			u = R.gen()
			H = u**3 + a1*u**2 + b2*u + c3
			M = L.extension(H.factor()[0][0], 'c')
			c = M.gen()
			R = M[FX.variable_name(), FY.variable_name()]
			x = R.gens()[0]
			y = R.gens()[1]
			good_equation = R(F0).subs({x:x+a,y:y+b+c*x})

			T = BerkovichTree(X)
			T = T.adapt_to_function(FX(factor))
			T.permanent_completion()

			for leaf in [leaf for leaf in T.leaves(subtrees=True) if leaf.root().type() == 'I' and not leaf.root() is X.infty()]:
				xi = leaf.root()
				print(xi)
				discoid = xi.approximation(require_maximal_degree=True).discoid()
				psi = discoid[0]
				d = psi.degree()
				print(len(v.extensions(L)))
				wL = [w for w in v.extensions(L) if w(psi.numerator()(a)) >= discoid[1]]
				assert len(wL) == 1, "unsure which valuation corresponds to this factor..."
				wL = wL[0]
				w = wL.extensions(M)[0] #it should not matter which extension to M we choose
				
				print([w(good_equation.monomial_coefficient(y**2*x**i)) for i in range(3)])
				print([w(good_equation.monomial_coefficient(y*x**i)) for i in range(4)])
				print([w(good_equation.monomial_coefficient(x**i)) for i in range(5)])
				A = minimum([AffineMap(i, w(good_equation.monomial_coefficient(y**2*x**i))) for i in range(3) if not good_equation.monomial_coefficient(y**2*x**i) == 0])
				B = minimum([AffineMap(i, w(good_equation.monomial_coefficient(y*x**i))) for i in range(4) if not good_equation.monomial_coefficient(y*x**i) == 0])
				C = minimum([AffineMap(i, w(good_equation.monomial_coefficient(x**i))) for i in range(5) if not good_equation.monomial_coefficient(x**i) == 0])
				D = maximum([AffineMap(0, 0), minimum([AffineMap(0, 1), A - QQ(1/3)*C, B - QQ(2/3)*C])])

				D_pos = restriction(D, 0, +Infinity)

				# make sure the approximation is good enough:
				r = D_pos._res[-1].start_point()
				while True:
					NP = npolygon(psi.numerator(), a, w)
					if NP.vertices()[0][0] == 1 or -NP.slopes()[0] >= r:
						break
					print("We have to improve an approximation, stand by...")
					discoid = xi.improved_approximation().discoid()
					psi = discoid[0]
				path_AT = AffinoidTree(X, root = xi, is_in = D(+Infinity) == 0)
				target, target_tree, lower_target, target_vertex = mu_locus_AT.position(xi)
				for f in reversed(D_pos._res[1:]):
					r = f.start_point()
					NP = npolygon(psi.numerator(), a, w)
					new_candidate = X.point_from_discoid(discoid[0], _discoid_radius(NP, r))
					if not first_leaf and new_candidate.is_leq(target):
						break
					assert len(new_candidate.valuation().extensions(FY)) == 1, "something is wrong"
					new_path_AT = AffinoidTree(X, root = new_candidate, children = [path_AT], is_in = f.start_value() == 0)
					path_AT.make_parent(new_path_AT)
					path_AT = new_path_AT

				if first_leaf:
					mu_locus_AT._is_in = D_pos._res[0].start_value() == 0
				else:
					assert mu_locus_AT._is_in == (D_pos._res[0].start_value() == 0)
				if first_leaf:
					mu_locus_AT.make_child(path_AT)
					path_AT.make_parent(mu_locus_AT)

					D_neg = restriction(D, -Infinity, 0)
					neg_path_AT = AffinoidTree(X, root = X.point_from_discoid(FX.gen(), D_neg._res[0].end_point() - 1), is_in = D(-Infinity) == 0)
					for f in (D_neg._res[:-1]):
						r = f.end_point()
						new_candidate = X.point_from_discoid(FX.gen(), r)
						new_neg_path_AT = AffinoidTree(X, root = new_candidate, children = [neg_path_AT], is_in = f.end_value() == 0)
						neg_path_AT.make_parent(new_neg_path_AT)
						neg_path_AT = new_neg_path_AT
					mu_locus_AT.make_child(neg_path_AT)
					neg_path_AT.make_parent(mu_locus_AT)

				else:
					if not target_vertex:
						new_lower_target = AffinoidTree(X, target, [lower_target, path_AT], target_tree, mu_locus_AT.is_in(target))
						lower_target.make_parent(new_lower_target)
						lower_target_index = target_tree._children.index(lower_target)
						target_tree._children[lower_target_index] = new_lower_target
					else:
						target_tree.make_child(path_AT)
						path_AT.make_parent(target_tree)

				first_leaf = False


		self._interior_locus = AffinoidDomainOnBerkovichLine(mu_locus_AT)
		return self._interior_locus



	def potential_tail_locus(self):

		if hasattr(self, "_potential_tail_locus"):
			return self._potential_tail_locus

		Y = self._curve
		FY = self._FY
		FX = self._FX
		K = self._K
		v = self._base_valuation
		X = self._X

		R = K[FX.variable_name(), FY.variable_name()]
		Q = R.fraction_field()
		S = Q[FX.variable_name() + '1', FY.variable_name() + '1', 'u']
		x0 = R.gens()[0] #think of this as the x-coordinate of the generic point around which we expand
		y0 = R.gens()[1] #think of this as the y-coordinate of the generic point
		t = S.gens()[0] #think of this as the variable in which expansions around x0 are written
		y = S.gens()[1] #this is the element whose reduction will generate the extension of residue fields
		u = S.gens()[2] #this will be used to construct the "p-approximation", the power series approximation of z

		F = R(FY.polynomial()).subs({x0:x0+t,y0:y0+y+t*u})
		level = 2
		# the level of the p-approximation, that is, the integer m, where u = u0+u1*t+...+u{m-1}*t^{m-1} 
		for i in range(1, level):
			ui = -F.coefficient({y:0, t:1, u:0})/F.coefficient({y:0, t:1, u:1})
			F = F(u = ui + t*u)

		h = R.fraction_field().hom([FX.gen(), FY.gen()])
		b0 = h(F.monomial_coefficient(y))
		C = [h(F.monomial_coefficient(t**i)) for i in range(F.coefficient({y:0, u:0}).degree(t) + 1)]

		print("b0=", b0)
		print("c2=", C[2])
		print("c3=", C[3])
		print("c4=", C[4])

		b0 = b0.norm()
		C = [C[i].norm() for i in range(len(C))]

		lambda_functions = [valuative_function(X, ([(b0, 3*(3-k)), (C[k], -(3-1)*3), (C[3], k*(3-1))], 0)) for k in range(level, len(C)) if k != 3]

		self._potential_tail_locus = UnionOfDomains([d.affinoid_domain() for d in lambda_functions])
		return self._potential_tail_locus




def _discoid_radius(NP, r):

	# Input: r is any rational number, NP is a Newton polygon
	#	     the first slope of NP is properly infinity, we check that r is not larger than the first slope
	# Output: The sum over the first d slopes of NP, except as soon as r is smaller than a given slope we replace that slope with r
	#         In particular, the first slope infinity is replaced with r
	# Example: Let NP be the Newton polygon with vertices (1, 3), (3, 0), (9, 0), let d=6 and r=3
	#          Then r is greater than all slopes except the first, so the output is 3 + 3/2 + 3/2 + 0 + 0 + 0 = 6
	#          If on the other hand r=1, then three slopes get replaced, so the output is 1 + 1 + 1 + 0 + 0 + 0 = 3

	if NP.vertices()[0][0] == 1: #the first slope is infinity
		slopes = [+Infinity] + [-x for x in NP.slopes()]
	else:
		assert NP.vertices()[0][0] == 0, "the Newton polygon has an unexpected shape"
		assert -NP.slopes()[0] >= r, "the approximation is not good enough"
		slopes = [-x for x in NP.slopes()]

	return sum([min(r, s) for s in slopes])


def npolygon(f, a, v):

	if a in f.parent():
		x = f.parent().gen()
	else:	
		A = a.parent()
		R = A['x']
		x = R.gen()
		f = R(f)
	f = f(x + a)

	points = []
	for i in range(0, f.degree() + 1):
		points.append((i, v(f[i])))

	return NewtonPolygon(points)




def random_quartic(large_coefficients=False, convenient_form=False):

	#returns a simple, randomly chosen quartic with coefficients that are small integers

	A = [_random_little_integer(large_coefficients) for i in range(3)]
	B = [_random_little_integer(large_coefficients) for i in range(4)]
	C = [_random_little_integer(large_coefficients) for i in range(5)]

	if convenient_form:
		A[2] = 0
		B[3] = 0
		C[0] = 0
		C[3] = 0

	R = QQ['x', 'y']
	x, y = R.gens()
	F = y**3 + y**2*sum([A[i]*x**i for i in range(3)]) + y*sum([B[i]*x**i for i in range(4)]) + sum([C[i]*x**i for i in range(5)])
	R = QQ['x']
	R = R['y']
	G = R(F)
	if not G.is_irreducible():
		print("This quartic is not irreducible, try again...")
		return random_quartic(large_coefficients, convenient_form)
	Y = SmoothProjectiveCurve(F)
	if not Y.genus() == 3:
		print("This quartic is not smooth, try again...")
		return random_quartic(large_coefficients, convenient_form)
	return Y

def _random_little_integer(large_coefficients=False):

	if not large_coefficients:
		if randint(0,100) < 50:
			return 0
		else:
			return randint(-3,3)
	return randint(-10, 10)




class AffineMap(SageObject):

	def __init__(self, a, b, sup=None, inf=None):

		assert not (a == +Infinity or a == -Infinity), "it doesn't make sense to have infinite slope"

		self._a = a
		self._b = b
		if sup is None:
			sup = +Infinity
		if inf is None:
			inf = -Infinity
		self._sup = sup
		self._inf = inf

	def __repr__(self):

		return "the affine function {}x + {} on the interval [{}, {}]".format(self._a, self._b, self._inf, self._sup)

	def __call__(self, x):

		assert x <= self._sup and x >= self._inf, "value is not in domain of this function"
		if not self._a == 0: #this formula is no good for a=0 and x=infinity
			return self._a*x + self._b
		else:
			return self._b

	def __mul__(self, q):

		return AffineMap(q*self._a, q*self._b, self._sup, self._inf)

	__rmul__ = __mul__

	def __add__(self, f):

		if isinstance(f, PiecewiseAffineMap):
			return f.__add__(self)

		assert self._inf == f._inf and self._sup == f._sup, "the functions don't have the same domain"
		return AffineMap(self._a + f._a, self._b + f._b, self._sup, self._inf)

	__radd__ = __add__

	def __sub__(self, f):

		if isinstance(f, PiecewiseAffineMap):
			return ((-1)*f).__add__(self)

		assert self._inf == f._inf and self._sup == f._sup, "the functions don't have the same domain"
		return AffineMap(self._a - f._a, self._b - f._b, self._sup, self._inf)


	def end_value(self):

		return self(self._sup)

	def start_value(self):

		return self(self._inf)

	def end_point(self):

		return self._sup

	def start_point(self):

		return self._inf

	def is_in_domain(self, x):

		return self._inf <= x and x <= self._sup

	def is_zero(self):

		return self._a == 0 and self._b == 0

	def is_infinity(self):

		return self._b == +Infinity


class PiecewiseAffineMap(SageObject):

	def __init__(self, res):

		for p in zip(res, res[1:]):
			print(p[0].end_value())
			print(p[1].start_value())
			assert p[0].end_value() == p[1].start_value(), "this function is not continuous"

		self._res = res

	def __repr__(self):

		return "the piecewise affine function made up of {}".format(self._res)

	def __call__(self, x):

		for f in self._res:
			if f.is_in_domain(x):
				return f(x)

	def __mul__(self, q):

		return PiecewiseAffineMap([q*f for f in self._res])

	__rmul__ = __mul__

	def __add__(self, f):

		if isinstance(self, PiecewiseAffineMap) and isinstance(f, AffineMap):
			return concatenate([selfi + restriction(f, selfi.start_point(), selfi.end_point()) for selfi in self._res])

		if isinstance(self, PiecewiseAffineMap) and isinstance(f, PiecewiseAffineMap):
			return concatenate([restriction(self, fi.start_point(), fi.end_point()) + fi for fi in f._res])

	__radd__ = __add__

	def __sub__(self, f):

		return self + (-1)*f


	def end_value(self):

		return self(self.end_point())

	def start_value(self):

		return self(self.start_point())

	def end_point(self):

		return self._res[-1].end_point()

	def start_point(self):

		return self._res[0].start_point()


	def separable_points(self):

		#returns the radii x where f(x)=0 and f has a kink
		#starts with the largest radius, ends with the smallest

		ret = []
		for i in range(len(self._res) - 2, -1, -1): #loops from the second to last index of self._res to 0
			if self._res[i].end_value() == 0 and (self._res[i].start_value() != 0 or self._res[i+1].end_value() !=0):
				ret.append(self._res[i].end_point())
		return ret

	def valleys(self):

		#returns closed intervals (may include plus or minus infinity or just be singletons) where this function is identically zero

		ret = []
		for i in range(len(self._res) - 1, -1, -1):
			if self._res[i].is_zero():
				ret.append((self._res[i].end_point(), self._res[i].start_point()))
			elif not i == 0 and not self._res[i-1].is_zero() and self._res[i].start_value() == 0 and self._res[i-1].end_value() == 0:
				ret.append((self._res[i].start_point(), self._res[i].start_point()))
		return ret

	def is_zero(self):

		return all([f.is_zero() for f in self._res])





def restriction(f, new_inf, new_sup):

	assert new_inf >= f.start_point() and new_sup <= f.end_point(), "the new domain is not contained in the old domain"

	if isinstance(f, AffineMap):
		return AffineMap(f._a, f._b, sup=new_sup, inf=new_inf)

	if isinstance(f, PiecewiseAffineMap):
		res = []
		for g in f._res:
			if new_inf >= g._sup or new_sup <= g._inf:
				continue
			else:
				res.append(restriction(g, max(new_inf, g._inf), min(new_sup, g._sup)))
		return PiecewiseAffineMap(res)



def intersection(f, g):

	# None if the slopes are identical -- including the case where f and g are identical

	if isinstance(f, AffineMap) and isinstance(g, AffineMap):
		if f._a == g._a:
			return None
		else:
			return (g._b - f._b)/(f._a - g._a)

def concatenate(l):

	# l is a list of functions f_1, f_2, ... which may be affine or piecewise affine functions such that the domain of f_i ends where the domain of f_{i+1} begins
	# returns the piecewise affine function obtained by putting all of them together

	res0 = []
	for f in l:
		if isinstance(f, AffineMap):
			res0.append(f)
		else:
			assert isinstance(f, PiecewiseAffineMap)
			res0 += f._res

	#merge identical functions
	res = [res0[0]]
	for f in res0[1:]:
		if f._a == res[-1]._a and f._b == res[-1]._b:
			res[-1]._sup = f._sup
		else:
			res.append(f)

	return PiecewiseAffineMap(res)


def minimum(functions):

	if len(functions) == 0:
		return AffineMap(0, +Infinity)

	if len(functions) > 2:
		return minimum([minimum(functions[0:2])] + functions[2:])
	if len(functions) == 1:
		return functions[0]
	assert len(functions) == 2

	f = functions[0]
	g = functions[1]

	assert f.start_point() == g.start_point() and f.end_point() == g.end_point(), "the functions don't have the same domain"

	if isinstance(f, AffineMap) and isinstance(g, AffineMap):
		m = intersection(f, g)
		if f.start_point() == -Infinity and f.end_point() == +Infinity:
			test_point = 0
		if f.start_point() == -Infinity and f.end_point() < +Infinity:
			test_point = f.end_point() - 1
		if f.start_point() > -Infinity and f.end_point() == +Infinity:
			test_point = f.start_point() + 1
		if f.start_point() > -Infinity and f.end_point() < +Infinity:
			test_point = (f.start_point() + f.end_point())/2

		if m is None or m <= f.start_point() or m >= f.end_point():
			if f(test_point) <= g(test_point):
				return f
			else:
				return g
		else:
			# now the intersection point m is in the closed interval on which f and g are defined
			if f.start_point() == -Infinity:
				test_point = m - 1
			else:
				test_point = (f.start_point() + m)/2


			if f(test_point) <= g(test_point):
				h1 = restriction(f, f.start_point(), m)
				h2 = restriction(g, m, f.end_point())
				return PiecewiseAffineMap([h1, h2])
			else:
				h1 = restriction(g, f.start_point(), m)
				h2 = restriction(f, m, f.end_point())
				return PiecewiseAffineMap([h1, h2])


	if isinstance(f, PiecewiseAffineMap) and isinstance(g, AffineMap):
		return concatenate([minimum([fi, restriction(g, fi.start_point(), fi.end_point())]) for fi in f._res])

	if isinstance(f, AffineMap) and isinstance(g, PiecewiseAffineMap):
		return minimum([g, f])

	if isinstance(f, PiecewiseAffineMap) and isinstance(g, PiecewiseAffineMap):
		return concatenate([minimum([restriction(f, gi.start_point(), gi.end_point()), gi]) for gi in g._res])


def maximum(functions):

	assert not len(functions) == 0, "there is nothing here"

	if len(functions) > 2:
		return maximum([maximum(functions[0:2])] + functions[2:])
	if len(functions) == 1:
		return functions[0]
	assert len(functions) == 2

	f = functions[0]
	g = functions[1]

	assert f.start_point() == g.start_point() and f.end_point() == g.end_point(), "the functions don't have the same domain"

	if isinstance(f, AffineMap) and isinstance(g, AffineMap):
		m = intersection(f, g)
		if f.start_point() == -Infinity and f.end_point() == +Infinity:
			test_point = 0
		if f.start_point() == -Infinity and f.end_point() < +Infinity:
			test_point = f.end_point() - 1
		if f.start_point() > -Infinity and f.end_point() == +Infinity:
			test_point = f.start_point() + 1
		if f.start_point() > -Infinity and f.end_point() < +Infinity:
			test_point = (f.start_point() + f.end_point())/2

		if m is None or m <= f.start_point() or m >= f.end_point():
			if f(test_point) >= g(test_point):
				return f
			else:
				return g
		else:
			if f.start_value() > g.start_value():
				h1 = restriction(f, f.start_point(), m)
				h2 = restriction(g, m, f.end_point())
				return PiecewiseAffineMap([h1, h2])
			else:
				h1 = restriction(g, f.start_point(), m)
				h2 = restriction(f, m, f.end_point())
				return PiecewiseAffineMap([h1, h2])

	if isinstance(f, PiecewiseAffineMap) and isinstance(g, AffineMap):
		return concatenate([maximum([fi, restriction(g, fi.start_point(), fi.end_point())]) for fi in f._res])

	if isinstance(f, AffineMap) and isinstance(g, PiecewiseAffineMap):
		return maximum([g, f])

	if isinstance(f, PiecewiseAffineMap) and isinstance(g, PiecewiseAffineMap):
		return concatenate([maximum([restriction(f, gi.start_point(), gi.end_point()), gi]) for gi in g._res])
