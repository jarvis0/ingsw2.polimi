open util/boolean
open util/integer

sig StringFormat {
}

sig DateValidInteger {
}

sig TimeValidInteger {
}

sig Date {
	year: DateValidInteger,
	month: DateValidInteger,
	day: DateValidInteger
} {
//	year > 2014
//	month >= 1 and month <= 7
//	day >= 1
//	(month = 4 || month = 6 || month = 9 || month = 11) implies day <= 30
//	month = 2 implies day <= 29
//	(month = 1 || month = 3 || month = 5 || month = 7 || month = 8 || month = 10 || month = 12) implies day <= 31
}

/*fact noEmptyDate {
	all d: Date | (#d.year = 1) and (#d.month = 1) and (#d.day = 1)
}*/

sig Time {
	hour: TimeValidInteger,
	minute: TimeValidInteger,
	second: TimeValidInteger
} {
/*	hour >= 0 and hour <= 23
	minute >= 0 and minute <= 59
	second >= 0 and second <= 59*/
}

sig Car {
	available: Bool,
	batteryLevel: Int,
	position: Position,
	charging: Bool,
	technicalIssue: set StringFormat,
	minutIssue: set StringFormat,
	numberPlate: StringFormat,
	seats: Int
} {
	batteryLevel >= 0
//	batteryLevel >= 0 and batteryLevel <= 100
//	batteryLevel <= 20 implies available = False
	/*batteryLevel > 20 implies available = True
	batteryLevel = 100 implies charging = False*/
	seats = 5
}

sig Position {
	latitude: Int,
	longitude: Int
} {
	latitude >= 0 and longitude >= 0
}

abstract sig User {
}

sig PaymentInformation extends User {
	paymentMethodName: String,
	userName: String,
	userSurname: String,
	cardNumber: String,
	expirationDate: String,
	cvv: String
}

sig PersonalInformation extends User {
	username: String,
	password: String,
	name: String,
	surname: String,
	nationality: String,
	birthDate: String,
	birthCity: String,
	id: String,
	phoneNumber: String,
	eMail: String
}

sig Reservation {
	reservationDate: Date,
	reservationTime: Time,
	doorsUnlockTime: Time,
	discountAmount: Int,
	feeAmount: Int,
	passengersNumber: Int,
	car: Car,
	ride: Ride
} {
	discountAmount >= 0
	feeAmount >= 0 //types of fees and discounts?
	passengersNumber >= 1 and passengersNumber <= 5
}

sig Ride {
	engineStartDate: Date,
	engineStartTime: Time,
	doorsLockDate: Date,
	doorsLockTime: Time
}

pred show {
}

run show for 5
