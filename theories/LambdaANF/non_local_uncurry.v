(* Non-local uncurrying. Not yet part of the CertiCoq project.
 * Author: Benjamin Quiring, 2023
 *)

(* BQ: 
   The general transformation is that for any fun_tag ft, it it is the
   case that lambdas for ft always take the form
   B = Fcons f ft ys (Efun (FCons g ft' zs e' FNil) (Ehalt g)) B'

   AND if it is the case that all applications are of the form

   Eletapp x f ft ys (Eapp g ft' zs)
   or 
   Eletapp x f ft ys (Eletapp y g ft' zs e)

   [TODO: is it required that ft <> ft'? A flow analysis will find that this is the case anyways]

   Then we can rewrite

   B = Fcons f ft ys (Efun (FCons g ft' zs e' FNil) (Ehalt g)) B'
   ~~~>
   B = Fcons f ft (ys @ zs) e' B'

   Eletapp x f ft ys (Eapp g ft' zs)
   ~~~>
   Eletapp x f ft (ys @ zs)
   
   and

   Eletapp x f ft ys (Eletapp y g ft' zs e)
   ~~~>
   Eletapp x f ft (ys @ zs) e


   Note that this
   - eliminates lambdas with the fun_tag ft'
   - does not perform iterated uncurrying to multiple fun_tags

   To perform iterated uncurrying, we'd first identify all the
   fun_tags ft with the above property.  Then, we rewrite them,
   ensuring that the inner lambdas ('g' in the example) are rewritten
   first. 
   I'm not sure of the degree to which this will complicate the proofs.

   We can't do the same trick as the existing transformation
   (introduce a new function in the body that is called on the
   combined list of args) as that relies on inlining to actually
   remove the curried function call.

*)
