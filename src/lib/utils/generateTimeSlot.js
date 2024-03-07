import moment from 'moment';

const shiftStartTime = (date) =>
  moment(date).set({ hours: 8, minutes: 0, seconds: 0, milliseconds: 0 });
const shiftEndTime = (date) =>
  moment(date).set({ hours: 23 , minutes: 59, seconds: 59, milliseconds: 999 });

export function generateTimeSlotsForShift(date, intervalInMinutes) {
  const startOfDay = moment(shiftStartTime(date));
  const endOfDay = moment(shiftEndTime(date));

  const timeSlots = [];
  let currentTimeSlot =  moment(startOfDay)

  while (currentTimeSlot <= endOfDay) {
    timeSlots.push(currentTimeSlot.format('hh:mm a'));
    currentTimeSlot.add(intervalInMinutes, 'minutes');
    if (currentTimeSlot.hours() > 23) {
      currentTimeSlot = moment(shiftStartTime(currentTimeSlot)).add(1, 'days');
    }
  }

  return timeSlots;
}
