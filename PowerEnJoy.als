sig Area {
}

sig Position {
}

abstract sig Notification {
	car: Car
}

abstract sig CumulativeNotification extends Notification {
}

sig TechnicalIssue extends CumulativeNotification {
}

sig MinorIssue extends CumulativeNotification {
	user: User
}

sig AlmostEmptyBatteryIssue extends Notification {
}

sig CarRedistributionNeeded extends Notification {
}

sig Car {
	position: Position,
	area: Area,
	cumulativeNotifications: set CumulativeNotification,
	almostEmptyBattery: lone AlmostEmptyBatteryIssue,
	redistributionNeeded: lone CarRedistributionNeeded
}

sig User {
	position: Position,
	personalInformation: PersonalInformation,
	paymentInformation: PaymentInformation,
	activeReservation: lone Reservation,
	invoices: set Invoice
}

sig PersonalInformation {
}

sig PaymentInformation {
}

sig Reservation {
	car: Car,
	ride: lone Ride
}

sig Ride {
	passengersNumber: Int,
} {
	passengersNumber >= 1 and passengersNumber <= 5
}

sig SafeParkingArea {
	area: Area,
	cars: set Car
}

sig SpecialParkingArea extends SafeParkingArea {
}

sig AFee extends Fee {
}

sig BFee extends Fee {
}

sig CFee extends Fee {
}

abstract sig Fee {
}

sig ADiscount extends Discount {
}

sig BDiscount extends Discount {
}

sig CDiscount extends Discount {
}

abstract sig Discount {
}

sig Invoice {
	fees: set Fee,
	discounts: set Discount
}

sig Paperwork {
}

sig Operator {
	paperworks: set Paperwork,
	notifications: set Notification
}

fact {

	//each notification is related to the corresponding car and the car has the set of his notifications
	all c: Car, n: CumulativeNotification | (n in c.cumulativeNotifications and c = n.car) or (n not in c.cumulativeNotifications and c != n.car)

	//each almost empty  issue is related to the corresponding car and the car has his almost empty battery issue
	all c: Car, empty: AlmostEmptyBatteryIssue | (c.almostEmptyBattery = empty and empty.car = c) or (c.almostEmptyBattery != empty and empty.car != c)

	// each redistribution needed notification is related to exactly one car
	all c: Car, r: CarRedistributionNeeded | (c.redistributionNeeded = r and r.car = c) or (c.redistributionNeeded != r and r.car != c)

	//no car with same position
	no c1, c2: Car | c1 != c2 and c1.position = c2.position

	//no user cannot have personal information and no user with the same personal information
	all personalInfo: PersonalInformation | (one u: User | u.personalInformation = personalInfo)

	//no user cannot have payment information
	all paymentInfo: PaymentInformation | (one u: User | u.paymentInformation = paymentInfo)

	//no ride without reservation and no ride of the same reservation
	all r: Ride | (one res: Reservation | res.ride = r)

	//two reservations have different cars
	no r1, r2: Reservation, c: Car | r1 != r2 and r1.car = c and r2.car = c

	//no reservation for technical issued cars
	all t: TechnicalIssue | (all r: Reservation | t not in r.car.cumulativeNotifications)

	//no reservation for almost empty battery cars
	all empty: AlmostEmptyBatteryIssue | (all r: Reservation | empty != r.car.almostEmptyBattery)

	//no reservation without user and no user with the same active reservation
	all r: Reservation | (one u: User | r = u.activeReservation)

	//riding cars are at the same position of the driver
	all ri: Ride | (one r: Reservation | (one u: User | r = u.activeReservation and r.car.position = u.position and r.ride = ri))

	//riding cars have not cars redistribution needed issue
	all redistrib: CarRedistributionNeeded | (all r: Reservation | redistrib != r.car.redistributionNeeded)

	//no safe parking area in the same area
	no park1, park2: SafeParkingArea | park1 != park2 and park1.area = park2.area

	//two safe parking areas has different cars
	no park1, park2: SafeParkingArea, c: Car | park1 != park2 and c in park1.cars and c in park2.cars

	//a car in a safe parking area have the same area
	no c1, c2: Car, park: SafeParkingArea | (c1 in park.cars and c2 in park.cars) and not (c1.area = c2.area and c1.area = park.area)

	//a car which is not in a ride must be in a safe parking area
	all c: Car, r: Reservation | no (r.ride & Ride) and r.car = c => c in SafeParkingArea.cars
	all c: Car | no (c & Reservation.car) => c in SafeParkingArea.cars

	//two users have two different invoices
	no u1, u2: User, i: Invoice | u1 != u2 and i in u1.invoices and i in u2.invoices

	//no invoice without user
	all i: Invoice | (one u: User | i in u.invoices)

	//no fee without invoice
	all f: Fee | (one i: Invoice | f in i.fees)

	//no discount without invoice
	all d: Discount | (one i: Invoice | d in i.discounts)

	//AFee only if no other fee/discount
	no a: AFee, i: Invoice | a in i.fees and ((i.fees - a) != none or i.discounts != none)

	//no C discount and B fee in the same invoice
	no c: CDiscount, b: BFee, i: Invoice | c in i.discounts and b in i.fees

	//no same type of fee in the same invoice
	all i: Invoice | #(AFee & i.fees) <= 1 and #(BFee & i.fees) <= 1 and #(CFee & i.fees) <= 1

	//no same type of discount in the same invoice
	all i: Invoice | #(ADiscount & i.discounts) <= 1 and #(BDiscount & i.discounts) <= 1 and #(CDiscount & i.discounts) <= 1

	//minor issue only if reservation or invoice for that user
	all m: MinorIssue | m.user.activeReservation.car = m.car or m.user.invoices != none

	//two paperworks have different operator
	no p1, p2: Paperwork, o: Operator | p1 != p2 and p1 in o.paperworks and p2 in o.paperworks

	//no paperwork without operator
	all p: Paperwork | (one o: Operator | p in o.paperworks)

	//no notification without operator
	all n: Notification | (one o: Operator | n in o.notifications)

	//all notifications are sent to all operators
	all o: Operator | o.notifications = Notification

	//no positions without users or cars
	User.position + Car.position = Position

	//no areas without cars or parking areas
	Car.area + SafeParkingArea.area = Area

	#Ride = 1
	#Operator = 0
	#User > 0
	#Reservation = 1
	#Car = 2
	#SafeParkingArea = 2
	#SpecialParkingArea = 2
	#Position > 0
	#Area > 0
}

assert noSameAlmostEmptyBatteryIssues {
	all c1, c2: Car | c1 != c2 <=> c1.almostEmptyBattery != c2.almostEmptyBattery
}
//check noSameAlmostEmptyBatteryIssues

assert noSameRedistributionNeededIssues {
	all c1, c2: Car | c1 != c2 <=> c1.redistributionNeeded != c2.redistributionNeeded
}
//check noSameRedistributionNeededIssues

assert noSameCumulativeNotifications {
	all c1, c2: Car | c1 != c2 <=> no c1.cumulativeNotifications & c2.cumulativeNotifications
}
//check noSameCumulativeNotifications

assert noCarsWithSamePosition {
	all c1, c2: Car | c1 != c2 <=> c1.position != c2.position
}
//check noCarsWithSamePosition

assert noReservationForSameCars {
	all r1, r2: Reservation | r1 != r2 <=> r1.car != r2.car
}
//check noReservationForSameCars

assert noRideIffUserAndCarAtSamePosition {
	all u: User | (lone r: Reservation | (lone ri: Ride | (r = u.activeReservation and r.car.position = u.position <=> r.ride = ri)))
}
//check noRideIffUserAndCarAtSamePosition

/*assert noRedistributionNeededForReservedCar {
	all r: Reservation | (one c: Car | (r.car = c implies c.redistributionNeeded not in CarRedistributionNeeded))
}does not work***************************
check noRedistributionNeededForReservedCar*/

pred show {
}

run show for 4
