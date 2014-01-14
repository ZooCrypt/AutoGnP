#!/usr/bin/env sage -python

from sage.all import *
import json
import sys
import traceback

###############################################################################
# Infrastructure functions: Debugging, json conversion
###############################################################################

debug_enabled = False

def debug(s):
  if debug_enabled:
    sys.stderr.write('### ')
    sys.stderr.write(s)
    sys.stderr.write('\n')
    sys.stderr.flush()

def _parseJSON(obj):
  """Convert unicode strings to standard strings"""
  if isinstance(obj, dict):
      newobj = {}
      for key, value in obj.iteritems():
          key = str(key)
          newobj[key] = _parseJSON(value)
  elif isinstance(obj, list):
      newobj = []
      for value in obj:
          newobj.append(_parseJSON(value))
  elif isinstance(obj, unicode):
      newobj = str(obj)
  else:
      newobj = obj
  return newobj

###############################################################################
# Parsing of monomials and polynomials
###############################################################################

def parseMonom(PR,m):
  """Parse the given monomial for the polynomial ring PR."""
  return reduce(lambda x, y: x * y, map(lambda v: PR.gens()[v], m) + [PR(1)])

def parsePoly(PR,p):
  """Parse the given polynomial for the polynomial ring PR."""
  return reduce(lambda x,y: x + y
               , map(lambda s: s[0] * parseMonom(PR,s[1]), p))

###############################################################################
# Utility functions for working with polynomials
###############################################################################

def coeff(f, m):
  """
  Returns coefficient of monomial m in f.
  Works with univariate polynomials and multivariate
  Singular polynomials.
  """
  try:
    return f.monomial_coefficient(m)
  except AttributeError:
    return f.coeff(m)

def monomials(f):
  """
  Returns the list of monomials in the polynomial f.
  """
  return [ s[1] for s in f ]

def extend_base_ring(PR_):
  """
  Extend the base ring of the polynomial ring PR_
  with a new variable pi. The new variable is last.
  """
  BF_ = PR_.base()
  gen_num = BF_.ngens() + 1 if BF_ != QQ else 1
  BF  = Frac(PolynomialRing(QQ,'p',gen_num))
  PR = PolynomialRing(BF, 'x', PR_.ngens())
  return PR

def divide_out(PR,f,d):
  """
  Given a monomial f and a monomial d, divide out
  d from f, i.e., return g such that g * m = f.
  Assumes that f is divisible by d.
  """
  assert(len(monomials(d)) == 1)
  assert(len(monomials(f)) == 1)
  d = monomials(d)[0]
  f = monomials(f)[0]
  new_deg = [ f.degrees()[j] - d.degrees()[j]
              for j in range(0,len(d.degrees())) ]
  return PR({tuple(new_deg):1})

def isVar(p):
  """
  Returns True if the polynomial p is just a variable, i.e., a monomial x with
  coefficient 1.
  """
  mons = monomials(p)
  return len(mons) == 1 and mons[0].degree() == 1 # FIXME: use coeff

def monoms(P):
  """Return all monomials in list of polynomials"""
  mons = list(set([ m for f in P for m in monomials(f) ]))
  mons.sort()
  return mons

def matrixOfPolys(ps, baseMonoms=None):
  """
  Returns matrix where rows are vector-representations of given polynomials
  with respect to the basis consisting of monomials occuring in the
  polynomials. Additionally, an augmented matrix is returned where the
  first row contains the basis.
  """
  mons = monoms(ps) if baseMonoms is None else baseMonoms
  return ( matrix([ [ g.monomial_coefficient(m) for m in mons] for g in ps ])
         , matrix(  [mons]
                  + [ [ g.monomial_coefficient(m) for m in mons] for g in ps ]))

def polyToList(f):
  """
  Convert the polynomial f to a list representation:
  [(ci,mi)] where each mi is represented
  as (x,e) for x^e.
  """
  return [ [ int(coeff(f,m))
           , [ [ int(str(x[0])[1:]), int(x[1]) ] for x in m.factor() ] ]
           for m in monomials(f) ]

###############################################################################
# Deducibility for Fq
###############################################################################

def make_param(PR,PR_,w,v,f):
  BF = PR.base()
  g = PR(0)
  for j, s in enumerate(f):
    # print "divide out:", s[1],w
    sys.stdout.flush()
    if s[1] % w == 0:
      g = g + PR(s[0]) * BF(v) * PR(PR_(divide_out(PR,s[1],w)))
      # print "divide out done:", s[1]/w
    else:
      g = g + PR(s[0]) * PR(s[1])
  return g

def make_param_deduc(PR_,w,known,secret):
  """
  Replace monomial w with a fresh parameter in all polynomials in known and in secret.
  Return new polynomial ring and new polynomial.
  """
  PR = extend_base_ring(PR_)
  BF = PR.base()
  v = BF.gens()[BF.ngens() - 1]
  known = [ [cf[0], make_param(PR,PR_,w,v,cf[1]) ] for cf in known ]
  secret = make_param(PR,PR_,w,v,secret)
  return PR,known,secret,(BF.ngens() - 1)

def monom_to_ctx(PR,abstr,m):
  BF = PR.base()
  vs = BF.gens()
  degs = m.degrees()
  # binary ^
  return [ ("^", abstr[j], degs[j]) for j in range(0,len(degs)) if degs[j] > 0]

def frac_to_ctx(PR,abstr,t):
  assert(t.denominator() == 1)
  t = t.numerator()
  res = []
  for s in t:
    # n-ary *
    res += [ ("*", [("int", int(s[0]))] + monom_to_ctx(PR,abstr,s[1])) ]
  # n-ary +
  return "+", res

def vec_to_ctx(PR,abstr, known, v):
  sys.stdout.flush()
  # n-ary *
  summands = [ ( "*"
               , [ known[j][0]
                 , frac_to_ctx(PR,abstr, v[0][j]) ] )
               for j in range(0,len(known))
               if v[0][j] != 0 ]
  # n-ary +
  return "+", summands

def solve_fq(PR,known,secret):
  """
  Solves the deducibility problem for field expressions.
  For now, the known term and secrets must be polynomials.

  Input:
    PR: polynomial ring
    known :: [(int,poly)] :
      list of known terms with corresponding recipes
      (parameter pi for the start).
    secret :: poly :
      polynomial for which deducibility is checked.
  """
  abstr = {}
  progress = True
  iteration = 0
  while progress:
    debug("Iteration: %i"%iteration)
    iteration += 1
    debug("  known: %s"% known)
    debug("  secret: %s"% secret)
    debug("  abstr: %s"% abstr)
    progress = False
    for j, ec in enumerate(known):
      # abstract variables (FIXME: abstract monomials)
      if isVar(ec[1]):
        (PR,known,secret,vidx) = make_param_deduc(PR,ec[1],known,secret)
        abstr[vidx] = ec[0] # store recipe for parameter
        progress = True
        break
  # express known polynomials and secrets
  known_polys = [cf[1] for cf in known ]
  base = monoms(known_polys+[secret])
  (KM,KM_aug) = matrixOfPolys(known_polys, baseMonoms=base)
  (SV,SV_aug) = matrixOfPolys([secret], baseMonoms=base)
  debug("known monomials:\n%s\n"%KM_aug)
  debug("secret monomials:\n%s\n"%SV_aug)
  res = KM.solve_left(SV)
  debug("result:\n%s\n"%res)
  # translate the result into a context
  sol = vec_to_ctx(PR,abstr, known, res)
  return sol

###############################################################################
# Interpreter for zoocrypt commands
###############################################################################

def interp(req):
  cmd = req['cmd']
  if cmd == "normFieldExp":
    F = Frac(PolynomialRing(QQ, 'x', max(1,req['varnum'])))
    #print type(F), varString(cmd['varnum'])
    fe = F(req['fieldexp'])
    #print type(fe), fe
    return { 'ok': True
           , 'numerator': polyToList(fe.numerator())
           , 'denominator': polyToList(fe.denominator()) }

  elif cmd == "solveFq":
    PR = PolynomialRing(QQ, 'x', max(1,req['varnum']))
    # list of known terms together with contexts
    known  = [ ( ("var",j), PR(req['known'][j]) ) for j in xrange(0,len(req['known'])) ]
    secret = PR(req['secret'])
    try:
      return { 'ok': True
             , 'res': solve_fq(PR,known,secret) }
    except ValueError:
      return { 'ok': False
             , 'res': "no solution" }


  elif cmd == "modReduceZero":
    PR = PolynomialRing(QQ, 'x', req['varnum'])
    a = PR(req['a'])
    b = PR(req['b'])
    return { 'ok': True
           , 'res': a % b == 0 }

  elif cmd == "exit":
    print "end\n"
    exit()

  else:
    return { 'ok': False
           , 'error': "unknown command" }

def main():
  try:
    while true:
      inp = sys.stdin.readline()
      debug(inp)
      cmd = json.loads(inp)
      cmd = _parseJSON(cmd)
      res = interp(cmd)
      debug(str(res))
      print(json.dumps(res))
      sys.stdout.flush()
  except Exception:
      if debug_enabled:
        traceback.print_exc()
      print(json.dumps({ 'ok': False
                       , 'error': "unknown error" }))

if __name__ == "__main__":
  #print interp(
  #  { 'cmd': "solveFq"
  #  , 'varnum': 5
  #  , 'known': [ "x3", "x0 + x1", "x1 + x2", "x4"]
  #  , 'secret': "(x0 - x2) * x3 * x4 * x0"
  #  })
  # print "interp", json.dumps(
  #   interp({ 'cmd': "normFieldExp"
  #          , 'varnum': 3
  #          , 'fieldexp': "(x0 - x2) * (x0 + x2) / ((x0 -x2)*(x1 + x0))"}))
  # print "interp", interp(
  #   { 'cmd': "modReduceZero"
  #   , 'varnum': 3
  #   , 'a': "(x0 - 1)*(x1 - 1)*(x2 - 1)"
  #   , 'b': "x0-1" })
  # print "interp", interp(
  #   { 'cmd': "modReduceZero"
  #   , 'varnum': 3
  #   , 'a': "(x0 - 1)*(x1 - 1)*(x2 - 1)"
  #   , 'b': "x0+1" })
  main()