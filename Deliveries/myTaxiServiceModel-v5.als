/*************** CLASSES ***************/

sig Queue { 
	first: one AvailableTaxiDriver,
	associatedArea : one TaxiArea 
}

abstract sig TaxiDriver {}

sig AvailableTaxiDriver extends TaxiDriver {
	next: lone AvailableTaxiDriver
}

sig BusyTaxiDriver extends TaxiDriver {}

sig Passenger {
} 

abstract sig Ride {
	driver : one BusyTaxiDriver,
	origins : some Location,
	passengers : some Passenger,
	destinations : some Location
} {
	origins not in destinations
}

sig SharedRide extends Ride {
} {
	#passengers < 4 &&
	#passengers > 1 &&
	#passengers = #destinations &&
	#passengers = #origins
}

sig SingleRide extends Ride {
}{
	#passengers = 1 &&
	#destinations = 1 &&
	#origins = 1
}

sig Location {}

sig TaxiArea {
	locations : some Location
}

sig Request_Reservation {
	requester : one Passenger,
	requesterArea : one TaxiArea,	
	associatedQueue : one Queue
}


/*************** CONSTRAINTS ***************/

// ensures that no taxi driver is the subsequent of himself inside a queue
fact nextNotReflexive { no n:TaxiDriver | n = n.next }

// ensures that each taxi driver is associated to only one queue
fact onlyOneQueuePerAvailableTaxiDriver {
	all d:AvailableTaxiDriver | one q:Queue | d in q.first.*next 
}

// ensures that the last taxi driver of the queue exists and is unique
fact notCyclicQueue { 
	no d:TaxiDriver | d in d.^next 
}

// ensures that all taxi drivers marked as busy are making only one ride
fact AllBusyTaxiDriverAreInARide {
	all d:BusyTaxiDriver | one r:Ride | r.driver = d
}

// ensures that all passengers in a ride are in only one ride
fact OnlyOneRidePerTimePerPassenger {
	all disj r1, r2:Ride | disj[r1.passengers, r2.passengers]
}

// ensures that every area has an associated queue
fact OneQueuePerLocationandViceversa {
	all disj q1, q2 : Queue | q1.associatedArea != q2.associatedArea
}

//ensures that every area contains different locations and a location is inside only one area
fact DisjointAreasContainsDifferentLocations {
	all disj a1, a2 : TaxiArea | disj[a1.locations, a2.locations]
}

// ensures that exists one and only one queue for every taxi area
fact OneQueuePerArea {
	all a:TaxiArea | one q: Queue | a = q.associatedArea
	all disj q1, q2 : Queue | q1.associatedArea != q2.associatedArea
}

// ensures that in a shared ride all origins belong to the same area and all destinations belong to the same area
fact OriginAndDestinationConsistency {
	all r: SharedRide | one a: TaxiArea | r.origins in a.locations
	all r: SharedRide | one a: TaxiArea | r.destinations in a.locations
}
// ensures that every passenger is associated to at most one active request or reservation
fact AtMostOneRequest_ReservationPerPassenger {
	no disj re1, re2 : Request_Reservation | re1.requester = re2.requester
}

//ensures that every request or reservation is associated to the queue belonging to the requester area
fact RightQueueForRequest_Reservation {
	all re:Request_Reservation | re.requesterArea = re.associatedQueue.associatedArea 
}


/*************** ASSERTIONS ***************/

// check that every taxi driver belong to one queue only
assert UniqueQueuePerTaxiDriver {
	no disj q1, q2:Queue | one d:AvailableTaxiDriver | (d in q1.first.*next and d in q2.first.*next)
}
check UniqueQueuePerTaxiDriver

// check that every busy taxi driver is making only one ride
assert OnlyOneRidePerTaxiDriver {
	no disj r1, r2 : Ride | r1.driver = r2.driver
}
check OnlyOneRidePerTaxiDriver

// check that every passenger in a ride is in only one ride
assert OnlyOneRidePerPassenger {
	no disj r1, r2 : Ride | not disj[r1.passengers, r2.passengers]
}
check OnlyOneRidePerPassenger

// check that an area corresponds to only one queue
assert OneAreaPerQueue {
	no disj q1,q2 : Queue | q1.associatedArea = q2.associatedArea
}
check OneAreaPerQueue

// check that disjoint areas involves different locations
assert OneAreaPerLocation {
	no disj a1,a2 : TaxiArea | not disj[a1.locations, a2.locations]
}
check OneAreaPerLocation

//check the corrispondency between taxi areas and queues
assert OneQueuePerArea {
	no a:TaxiArea | all q : Queue | a != q.associatedArea
}
check OneQueuePerArea

// check that for every shared ride, all the origins and destinations belong to the same 2 taxi zones
assert OriginsAndDestinationsAreConsistent {
	no disj a1, a2 : TaxiArea | one r:SharedRide | r.origins in (a1 + a2).locations
}
check OriginsAndDestinationsAreConsistent


/*************** PREDICATES ***************/
pred show() {
	#Queue > 1 &&
	#SharedRide > 1 &&
	#SingleRide > 1 &&
	#Request_Reservation > 1
}

run show for 6


pred showRides() {
	#Passenger>1 &&
	#TaxiArea > 1
}

run showRides for 9 but exactly 2 SharedRide
