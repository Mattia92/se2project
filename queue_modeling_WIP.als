/********** CLASSES **********/

sig Queue { 
	first: one AvailableTaxiDriver 
}

abstract sig TaxiDriver {}

sig AvailableTaxiDriver extends TaxiDriver {
	next: lone AvailableTaxiDriver
}

sig BusyTaxiDriver extends TaxiDriver {}

sig Passenger {} // TODO distinzione tra passeggeri in ride e passeggeri in richeista

sig Ride {
	driver : one BusyTaxiDriver,
	passenger : some Passenger
} {
	#passenger < 4
}


/********** CONSTRAINTS **********/

// ensures that no taxi driver is the subsequent of himself inside a queue
fact nextNotReflexive { no n:TaxiDriver | n = n.next }

// ensures that each taxi driver is associated to only one queue
fact onlyOneQueuePerAvailableTaxiDriver {
	all d:AvailableTaxiDriver | one q:Queue | d in q.first.*next 
}

// ensures that the last taxi driver of the queue exists and is unique
fact notCyclicQueue { no d:TaxiDriver | d in d.^next }

// non esiste un tassista che è in ride.driver e contemporaneamente è in queue.first.*next

// 
fact AllBusyTaxiDriverAreInARide {
	all d:BusyTaxiDriver | one r:Ride | r.driver = d
}
	

/********** ASSERTIONS **********/

// check that every taxi driver belong to one queue only
assert UniqueQueuePerTaxiDriver {
	no disj q1, q2:Queue | one d:TaxiDriver | (d in q1.first.*next and d in q2.first.*next)
}

check UniqueQueuePerTaxiDriver


/********** PREDICATES **********/
pred show() {}

run show for 10
