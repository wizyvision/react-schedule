import React from 'react';
import { useDrag } from 'react-dnd';
import {
  Divider,
  ListItem,
  ListItemText,
  Tooltip,
  Typography,
  darken,
} from '@mui/material';

import AppointmentContainer from '../../container/Appointment';
import { getAppointmentDuration } from '../../utils/getAppointments';
import Truncated from '../../container/Truncated';

function AppointmentItem(props) {
  const { appointment, width, height } = props;

  const [{ isDragging }, drag] = useDrag({
    type: 'APPOINTMENT',
    item: { appointment },
    collect: (monitor) => ({
      isDragging: !!monitor.isDragging(),
    }),
  });

  const color = appointment.user.color;
  const duration = getAppointmentDuration(appointment.schedule);

  const tooltipMessage = (
    <div>
      <span>{appointment.id}</span>
      <span>{appointment.title}</span>
      <span>{appointment.user.name} </span>
      <span>{duration}</span>
    </div>
  );

  console.log(appointment);

  return (
    <AppointmentContainer
      key={appointment.id}
      ref={drag}
      isDragging={isDragging}
      height={height}
      width={width}
      appointmentColor={color}
    >
      <div
        style={{
          padding: 4,
        }}
      >
        <Tooltip title={tooltipMessage}>
          <ListItemText
            primary={
              <div style={{ fontSize: '13px' }}>
                {appointment.user.name} 
                <span style={{color: darken(color, 0.5)}} > | </span>
                Duration: {duration}
              </div>
            }
            secondary={<div style={{display: 'flex', alignItems: 'center'}} >
              <Typography style={{fontSize: '500', fontSize: '16px'}} >
              WV-{appointment.id}
              </Typography>
               <Typography variant='body2' style={{fontSize: 'bold', marginLeft: 4, fontSize: '16px'}} >
               {appointment.title}
               </Typography>        
            </div>}
          />

        </Tooltip>
      </div>
    </AppointmentContainer>
  );
}

export default AppointmentItem;
