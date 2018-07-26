//package jason.stdlib;

import jason.JasonException;
import jason.asSemantics.DefaultInternalAction;
import jason.asSemantics.InternalAction;
import jason.asSemantics.TransitionSystem;
import jason.asSemantics.Unifier;
import jason.asSyntax.ListTerm;
import jason.asSyntax.NumberTerm;
import jason.asSyntax.NumberTermImpl;
import jason.asSyntax.Term;


/**
<p>Internal action: <b><code>.min</code></b>.

    <p>Description: gets the minimum value of a list of terms, using
    the "natural" order of terms. Between
different types of terms, the following order is
used:<br>

numbers &lt; atoms &lt; structures &lt; lists

<p>Parameters:<ul>
<li>+   list (list): the list where to find the minimal term.<br/>
<li>+/- minimal (term).
</ul>

<p>Examples:<ul>

<li> <code>.min([c,a,b],X)</code>: <code>X</code> unifies with
<code>a</code>.

<li>
<code>.min([b,c,10,g,f(10),[3,4],5,[3,10],f(4)],X)</code>:
<code>X</code> unifies with <code>5</code>.

<li>
<code>.min([3,2,5],2)</code>: true.

<li>
<code>.min([3,2,5],5)</code>: false.

<li>
<code>.min([],X)</code>: false.

</ul>

  @see jason.stdlib.concat
  @see jason.stdlib.delete
  @see jason.stdlib.length
  @see jason.stdlib.member
  @see jason.stdlib.nth
  @see jason.stdlib.sort
  @see jason.stdlib.max
  @see jason.stdlib.reverse

  @see jason.stdlib.difference
  @see jason.stdlib.intersection
  @see jason.stdlib.union

*/
public class rank extends DefaultInternalAction {

    private static InternalAction singleton = null;
    public static InternalAction create() {
        if (singleton == null)
            singleton = new rank();
        return singleton;
    }

    @Override public int getMinArgs() {
        return 3;
    }
    @Override public int getMaxArgs() {
        return 3;
    }

    @Override protected void checkArguments(Term[] args) throws JasonException {
        super.checkArguments(args); // check number of arguments
        if (!args[0].isList() || !args[1].isList())
            throw JasonException.createWrongArgument(this,"first and second arguments must be a list");
    }

    @Override
    public Object execute(TransitionSystem ts, Unifier un, Term[] args) throws Exception {
        checkArguments(args);

        ListTerm ss = (ListTerm)args[0];
        ListTerm prefs = (ListTerm)args[1];
        
        Integer max = Integer.MIN_VALUE;
        for (Term s: ss) {
        	int pos = prefs.indexOf(s);
        	if (pos > max) {
        		max = pos;
        	}
        }
        
        NumberTerm maxTerm = new NumberTermImpl(max);

        return un.unifies(args[2], maxTerm);
    }

    protected boolean compare(Term a, Term t) {
        return a.compareTo(t) > 0;
    }
}