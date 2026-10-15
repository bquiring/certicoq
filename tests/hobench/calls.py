# Instruments generated C to count calls: known calls name the function,
# closure calls go through a variable.  Calls to primitives are not counted.
import re, sys
src = open(sys.argv[1]).read()
pat = re.compile(r'\(\((value \(\*\)\([^()]*\))\) ([$\w]+)\)')
def rep(m):
    f = m.group(2)
    if f.startswith('prim_'):
        return m.group(0)
    kind = 'u' if f.startswith('$') else 'k'
    return '((%s) (ho_%s++, %s))' % (m.group(1), kind, f)
open(sys.argv[2], 'w').write('extern unsigned long long ho_k, ho_u;\n' + pat.sub(rep, src))
