#include <factory.h>
#include <assert.h>

using namespace std;

#define FOR0(i,n) for (i = 0; i < n; i++)

#define FOR1(i,n) for (i = 1; i < n+1; i++)

/* --------------------------------------------------------------------- */
/* Create new array of exponent vectors.                                 */
/* --------------------------------------------------------------------- */
long** new_expvecs(int nvars, int nterms) {
  long** evecs;
  int i, j;
  
  evecs = (long**) malloc(nterms * sizeof(long *));
  assert(evecs != NULL);
  FOR0(i, nterms) {
    evecs[i] = (long*) malloc(nvars * sizeof(long));
    assert(evecs[i] != NULL);
    FOR0(j,nvars) {
      evecs[i][j] = 0;
    }
  }
  return evecs;
}

/* --------------------------------------------------------------------- */
/* Free array of exponent vectors.                                       */
/* --------------------------------------------------------------------- */
void free_expvecs(long **evecs, int nterms) {
  int i;
  
  FOR0(i, nterms) {
    free(evecs[i]);
  }
  free(evecs);
}

/* --------------------------------------------------------------------- */
/* Create new array for coefficients.                                    */
/* --------------------------------------------------------------------- */
long* new_coeffs(int nterms) {
  long* coeffs;
  int i;
  coeffs = (long*) malloc(nterms * sizeof(long));
  FOR0(i,nterms) {
    coeffs[i] = 0;
  }
  assert(coeffs != NULL);
  return coeffs;
}

/* --------------------------------------------------------------------- */
/* Return number of terms interpreting f in ZZ[v_1,..,v_k].              */
/* --------------------------------------------------------------------- */
int getNumTerms(CanonicalForm f) {
  int tn = 0;
  int d = degree(f);
  if (d < 1) {
    return (f != 0?1:0);
  } else {
    for (int i = d; i >= 0; --i) {
      if (f[i] != 0) {
        tn += getNumTerms(f[i]);
      }
    }
    return tn;
  }
}

/* --------------------------------------------------------------------- */
/* Convert canonical form to distributed repr. (coeffs + exp. vectors)   */
/* --------------------------------------------------------------------- */
int
cfToDistr(CanonicalForm f, int var_idx, int* term_idx, long** expvecs, long* coeffs) {
  int i;
  int deg = degree(f);
  if (deg < 1) {
    coeffs[*term_idx] = f.intval(); // FIXME: use bignums
    *term_idx += 1;
    return *term_idx;
  } else {
    FOR0(i,deg+1) {
      if (f[i] != 0) {
        expvecs[*term_idx][var_idx] = i;
        cfToDistr(f[i], var_idx + 1, term_idx, expvecs, coeffs);
      }
    }
    return *term_idx;
  }
}

/* --------------------------------------------------------------------- */
/* Convert distributed repr. (coeffs + exp. vectors) to canonical form   */
/* --------------------------------------------------------------------- */
CanonicalForm distrToCf(int nvars, int nterms, long** expvecs, long* coeffs) {
  int i, j;
  CanonicalForm f(0);
  FOR0(i,nterms) {
    CanonicalForm t(coeffs[i]);
    FOR0(j, nvars) {
      t *= power(Variable(j+1),expvecs[i][j]);
    }
    f += t;
  }
  return f;
}

/* --------------------------------------------------------------------- */
/* Print distributed repr.                                               */
/* --------------------------------------------------------------------- */
void printDistr(int nvars, int nterms, long** expvecs, long* coeffs) {
  int i,j;
  FOR0(i,nterms) {
    if (i != 0) cout << "+";
    cout << coeffs[i];
    FOR0(j, nvars) {
      if (expvecs[i][j] > 0) {
        cout << "*" << "v_" << j+1;
        if (expvecs[i][j]!=1) {
          cout << "^" << expvecs[i][j];
        }
      }
    }
  }
  cout << endl;
}

extern "C" {

  /* --------------------------------------------------------------------- */
  /* C wrapper for printing.                                               */
  /* --------------------------------------------------------------------- */
  void
  wrap_print(int nvars, int nterms, long** expvecs, long* coeffs) {
    printDistr(nvars, nterms, expvecs, coeffs);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for exponent vectors allocation.                            */
  /* --------------------------------------------------------------------- */
  long**
  wrap_new_expvecs(int nvars, int nterms) {
    return new_expvecs(nvars, nterms);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for freeing exponent vectors.                               */
  /* --------------------------------------------------------------------- */
  void
  wrap_free_expvecs(long** expvecs, int nterms) {
    free_expvecs(expvecs, nterms);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for coefficient list allocation.                            */
  /* --------------------------------------------------------------------- */
  long*
  wrap_new_coeffs(int nterms) {
    return new_coeffs(nterms);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for coefficient list allocation.                            */
  /* --------------------------------------------------------------------- */
  void
  wrap_free_coeffs(long* coeffs) {
    free(coeffs);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for gcd computation.                                        */
  /* --------------------------------------------------------------------- */
  int
  wrap_gcd(int nvars,
           int nterms1, long** expvecs1, long* coeffs1,
           int nterms2, long** expvecs2, long* coeffs2,
           long*** expvecs_res, long** coeffs_res) {
    CanonicalForm g = distrToCf(nvars,nterms1,expvecs1,coeffs1);
    CanonicalForm f = distrToCf(nvars,nterms2,expvecs2,coeffs2);
    CanonicalForm h = gcd(g,f);
    cout << "gcd g: " << g << endl;
    cout << "gcd f: " << f << endl;
    cout << "gcd h: " << h << endl;

    int nvars_res  = getNumVars(h);
    int nterms_res = getNumTerms(h);

    *expvecs_res = new_expvecs(nvars_res, nterms_res);
    *coeffs_res  = new_coeffs(nterms_res);
    int term_idx = 0;
    cfToDistr(h,0,&term_idx,*expvecs_res,*coeffs_res);

    printDistr(nvars_res,nterms_res,*expvecs_res,*coeffs_res);
    return nterms_res;
  }
}

/* --------------------------------------------------------------------- */
/* C wrapper for factoring.                                              */
/* --------------------------------------------------------------------- */

/* --------------------------------------------------------------------- */
/* C wrapper for polynomial division.                                    */
/* --------------------------------------------------------------------- */

/* --------------------------------------------------------------------- */
/* C wrapper for polynomial remainder.                                   */
/* --------------------------------------------------------------------- */

/*
int main() {
    setCharacteristic( 0 );
    On( SW_USE_EZGCD );
    On( SW_RATIONAL );

    // Example for conversion from distributed form to recursive form by evaluation
    CanonicalForm g =
      CanonicalForm("2",10) * power(Variable(1),1) * power(Variable(2),2) * power(Variable(3),3);
    g += CanonicalForm("3",10) * power(Variable(1),3) * power(Variable(2),1) * power(Variable(3),2);
    g += CanonicalForm("4",10) * power(Variable(1),3) * power(Variable(2),7) * power(Variable(3),2);
    cout << "define cf g:  " << g << endl;

    // convert from CanonicalForm to OCaml interface repr.
    int nvars  = getNumVars(g);
    int nterms = getNumTerms(g);
    int** expvecs = new_expvecs(nvars, nterms);
    long* coeffs  = new_coeffs(nterms);
    cfToDistr(g,nvars,nterms,expvecs,coeffs);

    // print result
    cout << "distr g:      "; printDistr(nterms,nvars,expvecs,coeffs);
    
    // convert from CanonicalForm to OCaml interface repr.
    cout << "back to cf g: " << distrToCf(nvars,nterms,expvecs,coeffs) << endl;

    // convert from CanonicalForm to OCaml interface repr.
    CanonicalForm f = power(Variable(1),1) * power(Variable(2),10)*(Variable(3) + 2);
    int nvars2  = getNumVars(f);
    int nterms2 = getNumTerms(f);
    int** expvecs2 = new_expvecs(nvars2, nterms2);
    long* coeffs2  = new_coeffs(nterms2);
    cfToDistr(f,nvars2,nterms2,expvecs2,coeffs2);
    
    int** expvecs_res;
    long* coeffs_res;
    
    int i, nterms_res;
    FOR0(i,1000000) {
      nterms_res =
        wrap_gcd(nvars,nterms,expvecs,coeffs,nterms2,expvecs2,coeffs2,&expvecs_res,&coeffs_res);
      free_expvecs(expvecs_res,nterms_res);
      free(coeffs_res);
    }

    // cout << "gcd(g,f):     " << distrToCf(nvars,nterms_res,expvecs_res,coeffs_res) << endl;
    
}
*/
