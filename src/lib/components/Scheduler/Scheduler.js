import React from 'react';
import PropTypes from 'prop-types';

import { SchedulerProvider } from '../../context/SchedulerProvider';
import Calendar from '../Calendar';
import {
  AppointmentPropTypes,
  AppointmentDefaultValue,
} from '../../propTypes/AppointmentProps';
import { SlotPropTypes, SlotDefaultValues } from '../../propTypes/SlotProps';
import Header from '../Header';

/**
 * <p>Scheduler is composed of different libraries such as React-DND, moment, and MUI.</p>
 *
 * <p>This was created to accomodate the use case for scheduling apppointments for each user in each slot. The Scheduler component has the following functionalities:</p>
 *
 * <ul style="list-style: none;">
 * <li>1. Changing the date for Scheduler
 *  <ul style="list-style: none;">
 *    <li> 1.1. Can set the date for today
 *    <li> 1.2. Can change the date previously or the next date
 *    <li> 1.3. Manually changing the date in date picker
 *  </ul>
 * <li>2. Changing the duration of the appointment, before it was about to dropped inside the Scheduler
 * <li>3. Drag and drop from outside to inside of the Scheduler
 * <li>4. Drag and drop across the Scheduler
 * <li>5. Concurrent appointments
 * </ul>
 *  */
const Scheduler = (props) => {
  return (
    <SchedulerProvider {...props}>
      <div style={{ overflow: 'hidden', width: '100%'}} >
        <Header />
        <Calendar />
      </div>
    </SchedulerProvider>
  );
};

Scheduler.propTypes = {
  /**
   * Selected `groupId` to filter the users
   * @default ''
   */
  groupId: PropTypes.string,
  /**
   * `groups` is the list of groupId to filter the users
   * @default []
   */
  groups: PropTypes.array,
  /**
   * `users` is displayed in the first column. This prop is required.
   * @default []
   */
  users: PropTypes.array.isRequired,
  /**
   * `appointmentList` is a list of scheduled appointment with user. This list can be set with `onAppointmentChange`. This prop is required.
   * @default []
   */
  appointmentList: PropTypes.array.isRequired,
  /**
   * `onAppointmentChange` handles the changes for `appointmentList`. This prop is required.
   */
  onAppointmentChange: PropTypes.func.isRequired,
  /**
   * `durationOptions` is an array of numbers to be set for each appointment that can be dropped inside the scheduler. This prop is required.
   * @default [30,60,120]
   */
  durationOptions: PropTypes.array.isRequired,
  /**
   * `duration` is the selected duration among `durationOptions`. This prop is required.
   * @default 60
   */
  duration: PropTypes.number.isRequired,
  /**
   * Handles changing duration
   */
  onDurationChange: PropTypes.func,
  /**
   * Default date is set to current date
   */
  date: PropTypes.instanceOf(Date),
  /**
   * Handles to change the date
   */
  onDateChange: PropTypes.func,
  /**
   * Handles to go to the previous date
   */
  onPrevDate: PropTypes.func,
  /**
   * Handles to go to the next date
   */
  onNextDate: PropTypes.func,
  /**
   * This is to customized the Slots
   */
  SlotProps: SlotPropTypes,
  /**
   * This is to customized the Slots
   */
  AppointmentProps: AppointmentPropTypes,
  /**
   * Color is used to change the theme of the scheduler: `primary` | `secondary`
   * @default `primary`
   */
  color: PropTypes.string,
   /**
   * Color is used to change the theme of the scheduler: `primary` | `secondary`
   * @default `"Users"`
   */
  resourceLabel: PropTypes.string
};

Scheduler.defaultProps = {
  groupId: '',
  groups: [],
  users: [],
  appointmentList: [],
  durationOptions: [30, 60, 120],
  duration: 60,
  date: Date.now(),
  color: 'primary',
  SlotProps: SlotDefaultValues,
  AppointmentProps: AppointmentDefaultValue,
  resourceLabel: 'Userss'
};

export default Scheduler;
