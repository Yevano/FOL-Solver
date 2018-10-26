sealed class Term {
    abstract override fun toString() : String
    abstract override fun equals(other: Any?): Boolean
}

class Truth(val truth: Boolean) : Term() {
    override fun toString(): String {
        return if(truth) "⊤" else "⊥"
    }

    override fun equals(other: Any?): Boolean {
        return when(other) {
            is Truth -> truth == other.truth
            else -> false
        }
    }
}

class Variable(val name: String) : Term() {
    override fun toString(): String {
        return name
    }

    override fun equals(other: Any?): Boolean {
        return this === other
    }
}

class Implication(val lhs: Term, val rhs: Term) : Term() {
    override fun toString(): String {
        return "($lhs ⇒ $rhs)"
    }

    override fun equals(other: Any?): Boolean {
        return when(other) {
            is Implication -> this.lhs == other.lhs && this.rhs == other.rhs
            else -> false
        }
    }
}

class UniversalQuantifier(val variable: Variable, val body: Term) : Term() {
    override fun toString(): String {
        return "(∀${variable.name}. $body)"
    }

    override fun equals(other: Any?): Boolean {
        return when(other) {
            is UniversalQuantifier -> this.variable == other.variable && this.body == other.body
            else -> false
        }
    }
}

class ExistentialQuantifier(val variable: Variable, val body: Term) : Term() {
    override fun toString(): String {
        return "(∃${variable.name}. $body)"
    }

    override fun equals(other: Any?): Boolean {
        return when(other) {
            is ExistentialQuantifier -> this.variable == other.variable && this.body == other.body
            else -> false
        }
    }
}

class Negation(val rhs: Term) : Term() {
    override fun toString(): String {
        return "(¬$rhs)"
    }

    override fun equals(other: Any?): Boolean {
        return when(other) {
            is Negation -> this.rhs == other.rhs
            else -> false
        }
    }
}

class Disjunction(val lhs: Term, val rhs: Term) : Term() {
    override fun toString(): String {
        return "($lhs ∨ $rhs)"
    }

    override fun equals(other: Any?): Boolean {
        return when(other) {
            is Disjunction -> this.lhs == other.lhs && this.rhs == other.rhs
            else -> false
        }
    }
}

class Conjunction(val lhs: Term, val rhs: Term) : Term() {
    override fun toString(): String {
        return "($lhs ∧ $rhs)"
    }

    override fun equals(other: Any?): Boolean {
        return when(other) {
            is Conjunction -> this.lhs == other.lhs && this.rhs == other.rhs
            else -> false
        }
    }
}

class Abstraction(val variable: Variable, val type: Term, val body: Term) : Term() {
    override fun toString(): String {
        return "λ$variable: $type. $body"
    }

    override fun equals(other: Any?): Boolean {
        if(other is Abstraction) {
            return variable == other.variable && body == other.body
        }
        return false
    }
}

class Application(val lhs: Term, val rhs: Term) : Term() {
    override fun toString(): String {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun equals(other: Any?): Boolean {
        if(other is Application) {
            return lhs == other.lhs && rhs == other.rhs
        }
        return false
    }
}

fun elimImpl(term: Term) : Term {
    return when(term) {
        is Truth -> term
        is Variable -> term
        is Implication -> Disjunction(Negation(elimImpl(term.lhs)), elimImpl(term.rhs))
        is UniversalQuantifier -> UniversalQuantifier(term.variable, elimImpl(term.body))
        is ExistentialQuantifier -> ExistentialQuantifier(term.variable, elimImpl(term.body))
        is Negation -> Negation(elimImpl(term.rhs))
        is Disjunction -> Disjunction(elimImpl(term.lhs), elimImpl(term.rhs))
        is Conjunction -> Conjunction(elimImpl(term.lhs), elimImpl(term.rhs))
        else -> throw RuntimeException("Not supported")
    }
}

fun deMorgan(term: Term) : Term {
    return when(term) {
        is Truth -> term
        is Variable -> term
        is Implication -> Implication(deMorgan(term.lhs), deMorgan(term.rhs))
        is UniversalQuantifier -> UniversalQuantifier(term.variable, deMorgan(term.body))
        is ExistentialQuantifier -> ExistentialQuantifier(term.variable, deMorgan(term.body))
        is Negation -> when(term.rhs) {
            is Negation -> term.rhs.rhs
            is Disjunction -> Conjunction(Negation(deMorgan(term.rhs.lhs)), Negation(deMorgan(term.rhs.rhs)))
            is Conjunction -> Disjunction(Negation(deMorgan(term.rhs.lhs)), Negation(deMorgan(term.rhs.rhs)))
            is UniversalQuantifier -> ExistentialQuantifier(term.rhs.variable, Negation(deMorgan(term.rhs.body)))
            is ExistentialQuantifier -> UniversalQuantifier(term.rhs.variable, Negation(deMorgan(term.rhs.body)))
            else -> Negation(deMorgan(term.rhs))
        }
        is Disjunction -> Disjunction(deMorgan(term.lhs), deMorgan(term.rhs))
        is Conjunction -> Conjunction(deMorgan(term.lhs), deMorgan(term.rhs))
        else -> throw RuntimeException("Not supported")
    }
}

fun distribute(term: Term) : Term {
    return when(term) {
        is Truth -> term
        is Variable -> term
        is Implication -> Implication(distribute(term.lhs), distribute(term.rhs))
        is UniversalQuantifier -> UniversalQuantifier(term.variable, distribute(term.body))
        is ExistentialQuantifier -> ExistentialQuantifier(term.variable, distribute(term.body))
        is Negation -> Negation(distribute(term.rhs))
        is Disjunction -> when(term.rhs) { // TODO: Make this work for lhs, too.
            is Conjunction -> Conjunction(Disjunction(distribute(term.lhs), distribute(term.rhs.lhs)), Disjunction(distribute(term.lhs), distribute(term.rhs.rhs)))
            else -> when(term.lhs) {
                is Conjunction -> Conjunction(Disjunction(distribute(term.lhs.lhs), distribute(term.rhs)), Disjunction(distribute(term.lhs.rhs), distribute(term.rhs)))
                else -> Disjunction(distribute(term.lhs), distribute(term.rhs))
            }
        }
        is Conjunction -> Conjunction(distribute(term.lhs), distribute(term.rhs))
        else -> throw RuntimeException("Not supported")
    }
}

class AtomicTerm {
    val truthful: Boolean
    val term: Term

    constructor(truthful: Boolean, term: Term) {
        this.truthful = truthful

        when(term) {
            is Variable -> this.term = term
            is Truth -> this.term = term
            else -> throw RuntimeException("Cannot negate term.")
        }
    }
}

class ConjunctiveNormalForm(var set: HashSet<HashSet<AtomicTerm>>) {
    fun cancelDisjunctiveNegatives(terms: HashSet<AtomicTerm>) : HashSet<AtomicTerm> {
        val result = HashSet<AtomicTerm>()

        for(e in terms) {
            result.add(e)
            for(f in terms.filter { g -> e != g }) {
                if(e.term == f.term) {
                    if(e.truthful != f.truthful) {
                        return hashSetOf(AtomicTerm(true, Truth(true)))
                    }
                }
            }
        }

        return result
    }

    fun simplify() {
        val newSet = HashSet<HashSet<AtomicTerm>>()

        for(innerSet in set) {
            newSet.add(cancelDisjunctiveNegatives(innerSet))
        }

        set = newSet
    }

    fun truthValue() : Boolean? {
        fun checkOR(innerSet: HashSet<AtomicTerm>) : Boolean? {
            var b: Boolean? = null

            for(atomicTerm in innerSet) {
                when(atomicTerm.term) {
                    is Truth -> when(atomicTerm.term.truth) {
                        true -> return true
                        false -> b = false
                    }
                }
            }

            return b
        }

        for(innerSet in set) {
            when(checkOR(innerSet)) {
                false -> return false
                null -> return null
            }
        }

        return true
    }

    override fun toString(): String {
        val sb = StringBuilder("(")


        val firstSet = set.stream().findFirst().get()
        val firstTerm = firstSet.stream().findFirst().get()
        sb.append(if(firstTerm.truthful) "" else "¬")
        sb.append(firstTerm.term)

        for(atomicTerm in firstSet.stream().skip(1)) {
            sb.append(" ∨ ")
            sb.append(if(atomicTerm.truthful) "" else "¬")
            sb.append(atomicTerm.term)
        }

        for(innerSet in set.stream().skip(1)) {
            sb.append(") ∧ (")

            val firstTerm = innerSet.stream().findFirst().get()
            sb.append(if(firstTerm.truthful) "" else "¬")
            sb.append(firstTerm.term)

            for(atomicTerm in innerSet.stream().skip(1)) {
                sb.append(" ∨ ")
                sb.append(if(atomicTerm.truthful) "" else "¬")
                sb.append(atomicTerm.term)
            }
        }

        sb.append(")")
        return sb.toString()
    }
}

fun conjunctiveTreeToSet(term: Conjunction) : Set<Disjunction> {
    return when(term.lhs) {
        is Conjunction -> conjunctiveTreeToSet(term.lhs)
        is Disjunction -> setOf(term.lhs)
        else -> throw RuntimeException("")
    }.union(when(term.rhs) {
        is Conjunction -> conjunctiveTreeToSet(term.rhs)
        is Disjunction -> setOf(term.rhs)
        else -> throw RuntimeException("")
    })
}

fun disjunctiveTreeToSet(term: Disjunction) : Set<Term> {
    return when(term.lhs) {
        is Disjunction -> disjunctiveTreeToSet(term.lhs)
        is Negation -> setOf(term.lhs)
        is Variable -> setOf(term.lhs)
        is Truth -> setOf(term.lhs)
        else -> throw RuntimeException("")
    }.union(when(term.rhs) {
        is Disjunction -> disjunctiveTreeToSet(term.rhs)
        is Negation -> setOf(term.rhs)
        is Variable -> setOf(term.rhs)
        is Truth -> setOf(term.rhs)
        else -> throw RuntimeException("")
    })
}

fun toCNF(term: Term) : ConjunctiveNormalForm {
    val conjunctiveSet : Set<Disjunction>
    if(term is Conjunction) {
        conjunctiveSet = conjunctiveTreeToSet(term)
    } else {
        conjunctiveSet = hashSetOf(when(term) {
            is Disjunction -> term
            else -> throw RuntimeException("Bandaid") // TODO: Fix this.
        })
    }

    val outerSet = HashSet<HashSet<AtomicTerm>>()

    for(t in conjunctiveSet) {
        val disjunctiveSet = disjunctiveTreeToSet(t)
        val innerSet = HashSet<AtomicTerm>()

        for(u in disjunctiveSet) {
            innerSet.add(when(u) {
                is Variable -> AtomicTerm(true, u)
                is Negation -> AtomicTerm(false, u.rhs)
                is Truth -> AtomicTerm(true, u)
                else -> throw RuntimeException("Unexpected term.")
            })
        }

        outerSet.add(innerSet)
    }

    return ConjunctiveNormalForm(outerSet)
}

fun applyWhileChanging(t: Term, f: (Term) -> Term) : Term {
    var term = t
    var newTerm = term
    do {
        term = newTerm
        newTerm = f(term)
    } while(term != newTerm)
    return term
}

fun evaluateFOL(t: Term) : Boolean? {
    var term = t
    term = applyWhileChanging(term, ::elimImpl)
    term = applyWhileChanging(term, ::deMorgan)
    term = applyWhileChanging(term, ::distribute)

    val cnf = toCNF(term)
    cnf.simplify()
    return cnf.truthValue()
}

fun main(args: Array<String>) {
    val a = Variable("A")
    val b = Variable("B")
    val c = Variable("C")

    // A => B => ((A => B => C) => C)
    // var term : Term = Implication(a, Implication(b, Implication(Implication(a, Implication(b, c)), c)))

    // A => B => ((A => C) => (B => C) => C)
    var term : Term = Implication(a, Implication(a, Implication(Implication(a, c), Implication(Implication(b, c), c))))

    println("Eliminating implications.")

    term = applyWhileChanging(term, ::elimImpl)

    println("Applying DeMorgan's Law.")

    term = applyWhileChanging(term, ::deMorgan)

    println("Distributing ORs inwards over ANDs.")

    term = applyWhileChanging(term, ::distribute)

    if(term is Conjunction) {
        val cnf = toCNF(term)
        println("Convert to CNF.")
        println(cnf)

        println("Simplify terms.")
        cnf.simplify()
        println(cnf)

        println("Truth value: " + when(cnf.truthValue()) {
            true -> "⊤"
            false -> "⊥"
            null -> "unknown"
        })
    }

    val zenTerm = Abstraction(a, Truth(true), a)
    val application = Application(zenTerm, b)
    println(reduceApplication(application))
}