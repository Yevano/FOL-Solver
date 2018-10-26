import java.lang.RuntimeException

fun betaReduce(term: Term, variable: Variable, substitute: Term) : Term {
    return when(term) {
        variable -> substitute
        is Truth -> term
        is Variable -> term
        is Implication -> Implication(betaReduce(term.lhs, variable, substitute), betaReduce(term.rhs, variable, substitute))
        is UniversalQuantifier -> UniversalQuantifier(term.variable, betaReduce(term.body, variable, substitute))
        is ExistentialQuantifier -> ExistentialQuantifier(term.variable, betaReduce(term.body, variable, substitute))
        is Negation -> Negation(betaReduce(term.rhs, variable, substitute))
        is Disjunction -> Disjunction(betaReduce(term.lhs, variable, substitute), betaReduce(term.rhs, variable, substitute))
        is Conjunction -> Conjunction(betaReduce(term.lhs, variable, substitute), betaReduce(term.rhs, variable, substitute))
        is Abstraction -> Abstraction(term.variable, betaReduce(term.type, variable, substitute), betaReduce(term.body, variable, substitute))
        is Application -> Application(betaReduce(term.lhs, variable, substitute), betaReduce(term.rhs, variable, substitute))
    }
}

fun reduceApplication(application: Application) : Term {
    return when(application.lhs) {
        is Abstraction -> {
            val abstraction = application.lhs
            val folTerm = Implication(application.rhs, abstraction.type)
            if(evaluateFOL(folTerm) != true) {
                throw RuntimeException("Type ${abstraction.type} does not accept ${application.rhs}.")
            }
            betaReduce(abstraction.body, abstraction.variable, application.rhs)
        }
        is Application -> reduceApplication(Application(reduceApplication(application.lhs), application.rhs))
        else -> application
    }
}

fun evaluateZenith(t: Term) : Term {
    return applyWhileChanging(t) {
        if(it is Application) {
            reduceApplication(it)
        }
        it
    }
}