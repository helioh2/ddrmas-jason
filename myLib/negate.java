

import jason.asSemantics.DefaultInternalAction;
import jason.asSemantics.InternalAction;
import jason.asSemantics.TransitionSystem;
import jason.asSemantics.Unifier;
import jason.asSyntax.Literal;
import jason.asSyntax.LiteralImpl;
import jason.asSyntax.Term;

/**
  <p>Internal action: <b><code>.literal</code></b>.

  <p>Description: checks whether the argument is a literal,
  e.g.: "p", "p(1)", "p(1)[a,b]", "~p(1)[a,b]".

  <p>Parameter:<ul>
  <li>+ argument (any term): the term to be checked.<br/>
  </ul>

  <p>Examples:<ul>
  <li> <code>.literal(b(10))</code>: true.
  <li> <code>.literal(b)</code>: true.
  <li> <code>.literal(10)</code>: false.
  <li> <code>.literal("Jason")</code>: false.
  <li> <code>.literal(X)</code>: false if X is free, true if X is bound to a literal.
  <li> <code>.literal(a(X))</code>: true.
  <li> <code>.literal([a,b,c])</code>: false.
  <li> <code>.literal([a,b,c(X)])</code>: false.
  </ul>

  @see jason.stdlib.atom
  @see jason.stdlib.list
  @see jason.stdlib.number
  @see jason.stdlib.string
  @see jason.stdlib.structure
  @see jason.stdlib.ground
*/
public class negate extends DefaultInternalAction {

    private static InternalAction singleton = null;
    public static InternalAction create() {
        if (singleton == null)
            singleton = new negate();
        return singleton;
    }

    @Override public int getMinArgs() {
        return 2;
    }
    @Override public int getMaxArgs() {
        return 2;
    }

    @Override
    public Object execute(TransitionSystem ts, Unifier un, Term[] args) throws Exception {
        checkArguments(args);
        Literal myLiteral = new LiteralImpl((Literal) args[0]);
        Literal newLiteral = null;
        if (myLiteral.negated()) {
        	newLiteral = myLiteral.setNegated(false);
        } else {
        	newLiteral = myLiteral.setNegated(true);
        }
//        Literal negation = new LiteralImpl(false, l)
        return un.unifies(args[1], newLiteral);
    }
}
