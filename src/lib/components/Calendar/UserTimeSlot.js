import React, { useState } from 'react';
import { useDrop } from 'react-dnd';
import moment from 'moment';
import { useTheme } from '@mui/material';

import {
  getFilteredAppointments,
  getSortAppointments,
  getUpdatedAppointments,
} from '../../utils/getAppointments';
import { getAppointmentWidth, getDurationWidth, getSlotWidth, slotBg } from '../../utils/getAppointmentStyle';

import { useSchedulerContext } from '../../context/SchedulerProvider';
import Slot from '../../container/Slot';
import Appointments from './Appointments';
import { WIDTH } from '../../constants/appointment';

function UserTimeSlot(props) {
  const { user, timeSlot, index } = props;
  const {
    appointmentList,
    onAppointmentChange,
    duration,
    date,
    SlotProps,
    color,
    customCanDrop,
  } = useSchedulerContext();
  const { secondaryDuration = 30, slotBackground } = SlotProps || {}

  const theme = useTheme();

  const dropRef = React.useRef(null);
  const [hoveredItem, setHoveredItem] = useState(null)
  const [{ isOver, canDrop, item }, drop] = useDrop({
    accept: 'APPOINTMENT',
    canDrop: (appointment) => {
      return customCanDrop ? customCanDrop(appointment) : true
    },
    hover: (item, monitor, component) => {
      const clientOffset = monitor.getClientOffset();
      const dropTargetRect = dropRef.current.getBoundingClientRect();
      const appointmentWidth = getAppointmentWidth(timeSlot, item.schedule?.startDate, item.schedule?.endDate, secondaryDuration)
      if (
        clientOffset.x >= dropTargetRect.left  &&
        clientOffset.x <= dropTargetRect.right &&
        clientOffset.y >= dropTargetRect.top &&
        clientOffset.y <= dropTargetRect.bottom &&
        clientOffset.x <= dropTargetRect.right + appointmentWidth
      ) {
        setHoveredItem(item);
      } else {
        setHoveredItem(null);
      }
    },
    drop: (appointment, monitor) => {
      const dropTargetRect = dropRef.current.getBoundingClientRect();
      // Get the cursor offset
      const clientOffset = monitor.getClientOffset();
      const appointmentWidth = getAppointmentWidth(timeSlot, appointment.schedule?.startDate, appointment.schedule?.endDate, secondaryDuration)
      if (
        clientOffset.x >= dropTargetRect.left &&
        clientOffset.x <= dropTargetRect.right &&
        clientOffset.y >= dropTargetRect.top &&
        clientOffset.y <= dropTargetRect.bottom 
      ) {
        const droppedAppointment = appointment.appointment;
        const updatedAppointments = getUpdatedAppointments(
          appointmentList,
          droppedAppointment,
          date,
          timeSlot,
          duration,
          user
        );
        onAppointmentChange(updatedAppointments);
      }
    },
    collect: (monitor) => ({
      isOver: monitor.isOver({ shallow: true }),
      canDrop: monitor.canDrop(),
      item: monitor.getItem()
    }),
  });

  const sortedAppointments = getSortAppointments(appointmentList, user);
  const concurrentAppointments = {};
  let previousConcurrentCount = 0;
  sortedAppointments.forEach((event, index) => {
    const startDate = moment(event.schedule.startDate);
    const count = sortedAppointments.reduce((acc, otherEvent, otherIndex) => {
      if (
        index !== otherIndex &&
        moment(otherEvent.schedule.startDate).isBefore(startDate) &&
        moment(otherEvent.schedule.endDate).isAfter(startDate)
      ) {
        return acc + 1;
      }
      return acc;
    }, 0);
    concurrentAppointments[event.id] =
      count > 0 ? count + previousConcurrentCount : 0;
    // Update previousConcurrentCount for the next event
    previousConcurrentCount = count > 0 ? concurrentAppointments[event.id] : 0;
  });

  const filteredAppointments = getFilteredAppointments(
    appointmentList,
    user,
    timeSlot,
    date,
    secondaryDuration,
    concurrentAppointments
  );

  const [clickedIndex, setClickedIndex] = useState(null);
  const handleClick = (_index) => {
    setClickedIndex(_index);
  };

  // console.log(clickedIndex === index)
  // console.log(index)

  const width = getSlotWidth(secondaryDuration);
  
  const durationWidth = getDurationWidth(timeSlot, duration, width)
  const bg = slotBg(canDrop, isOver, slotBackground, theme, color);

  const calculateIsOverWidth = () => {
    const start = moment(item?.appointment?.schedule?.startDate)
    const end = moment(item?.appointment?.schedule?.endDate)

    const existingDuration = moment
    .duration(end.diff(start))
    .asMinutes();

    if(existingDuration){
      return getDurationWidth(timeSlot, existingDuration, width)
    }
    return getDurationWidth(timeSlot, duration, width)
  }

  drop(dropRef);
  return (
    <Slot colSpan={1} ref={dropRef}  index={index} width={width || '100%'}  onClick={() => handleClick(index)}>
      <div ref={dropRef} style={{ overflow: 'visible', width: width, height: '100%',}} >
       {(isOver) && <div style={{backgroundColor: bg, width: calculateIsOverWidth(),  height: '100%', position: 'absolute', top: 0, zIndex: 10}} ></div>}
        {/* {clickedIndex === index && <div style={{width: durationWidth,
              height: '100%',
              backgroundColor: 'red',
              position: 'absolute',
              top: 0,
              left: 0,}} ></div>} */}
        <Appointments
          appointments={filteredAppointments}
          secondaryDuration={secondaryDuration}
          timeSlot={timeSlot}
        />
      </div>
    </Slot>
  );
}

export default UserTimeSlot;
