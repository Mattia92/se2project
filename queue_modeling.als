sig Queue { first: TaxiDriver }

sig TaxiDriver { next: lone TaxiDriver }

fact nextNotReflexive { no n:TaxiDriver | n = n.next }

fact allQueuesContainsDifferentTaxiDrivers {
	all d:TaxiDriver | one q:Queue | d in q.first.*next 
}

fact notCyclicQueue { no d:TaxiDriver | d in d.^next }

pred show() {}

run show for 20
