/********** CLASSES **********/

sig Queue { first: TaxiDriver }

sig TaxiDriver { next: lone TaxiDriver }



/********** CONSTRAINTS **********/

// ensures that no taxi driver is the subsequent of himself inside a queue
fact nextNotReflexive { no n:TaxiDriver | n = n.next }

// ensures that each taxi driver is associated to only one queue
fact onlyOneQueuePerTaxiDriver {
	all d:TaxiDriver | one q:Queue | d in q.first.*next 
}

// ensures that the last taxi driver of the queue exists and is unique
fact notCyclicQueue { no d:TaxiDriver | d in d.^next }

pred show() {}

run show for 15
