import moment from 'moment';
import {
  HEIGHT,
  HEIGHT_REDUCTION_CONCURRENT,
  MIN_HEIGHT,
  WIDTH,
} from '../constants/appointment';
import {
  dropBackgroundColor,
  overBackgroundColor,
  slotBackgroundColor,
} from './theme';

export const slotBg = (canDrop, isOver, slotBackground, theme, color = 'primary') => {
  const { dropBg, overBg } = slotBackground || {};

  const slotColor = slotBackgroundColor(theme);
  const overColor = overBackgroundColor(theme);
  const dropColor = dropBackgroundColor(theme);

  let backgroundColor = slotColor[color] || 'transparent';
  if (canDrop && isOver) {
    backgroundColor = dropBg || dropColor[color]; // Highlight color when canDrop and isOver
  } else if (canDrop) {
    backgroundColor = overBg || overColor[color]; // Color when only canDrop is true
  }
  return backgroundColor;
};

export const getSlotWidth = (slotDuration) => {
  switch (slotDuration) {
    case 15:
      return WIDTH / 2;
    default:
      return WIDTH;
  }
};

export const getAppointmentWidth = (timeSlot, start, end, duration) => {
  const slotStart = moment(timeSlot, 'hh:mm a');
  const slotEnd = moment(slotStart).add(duration, 'minutes');

  const appointmentStart = moment(start);
  const appointmentEnd = moment(end);

  const totalMinutesInSlot = moment
    .duration(slotEnd.diff(slotStart))
    .asMinutes();
  const appointmentDuration = moment
    .duration(appointmentEnd.diff(appointmentStart))
    .asMinutes();

  const width =
    (appointmentDuration / totalMinutesInSlot) * getSlotWidth(duration);

  return width + 'px';
};

export const getDurationWidth = (timeSlot, duration, slotWidth) => {
   // Parse the timeSlot to a moment object
   const slotStart = moment(timeSlot, 'hh:mm a' ); // Assuming timeSlot is in 24-hour format

   // Calculate the end time of the time slot based on the duration
   const slotEnd = moment(slotStart).add(duration, 'minutes');
 
   // Calculate the width based on the difference between slotStart and slotEnd
   const totalMinutesInSlot = slotEnd.diff(slotStart, 'minutes');
   const width = (totalMinutesInSlot / 30) * slotWidth; // Assuming slotWidth is in pixels
   return width;
}

export const getAppointmentHeight = (concurrentCount) => {
  let height = HEIGHT;
  const computedHeight = HEIGHT - (HEIGHT_REDUCTION_CONCURRENT * concurrentCount);
  height = Math.max(MIN_HEIGHT, computedHeight);
  return height;
};
